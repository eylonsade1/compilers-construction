(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;
  
  let remove_elt e l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x::xs when e = x -> go xs acc
      | x::xs -> go xs (x::acc)
    in go l [];;
  
  let remove_duplicates l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x :: xs -> go (remove_elt x xs) (x::acc)
    in go l [];;

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

    let getString = function
    |ScmVar(str) -> str
    |_ -> "";;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmConst(sexpr) -> ScmConst'(sexpr)
      | ScmVar(str) -> ScmVar'((tag_lexical_address_for_var str params env))
      | ScmIf(expr1,expr2,expr3) -> ScmIf'((run expr1 params env),(run expr2 params env),(run expr3 params env))
      | ScmSeq(exprList) -> ScmSeq'((List.map (fun exp -> (run exp params env)) exprList))
      | ScmSet(expr1, expr2) -> ScmSet'((tag_lexical_address_for_var (getString expr1) params env),(run expr2 params env))
      | ScmDef(expr1, expr2) -> ScmDef'((tag_lexical_address_for_var (getString expr1) params env),(run expr2 params env))
      | ScmOr(exprList) -> ScmOr'((List.map (fun exp -> (run exp params env)) exprList))
      | ScmLambdaSimple(stringList, expr) -> ScmLambdaSimple'(stringList, (run expr stringList (params::env)))
      | ScmLambdaOpt(stringList, str, expr) -> ScmLambdaOpt'(stringList, str, (run expr (List.append stringList [str]) (params::env)))
      | ScmApplic(operator, exprList) -> ScmApplic'((run operator params env), (List.map (fun exp -> (run exp params env)) exprList))
   in 
   run pe [] [];;

  (* [1,2,3]  -> ([1,2],3) *)   
  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
    match pe with
    | ScmConst'(sexpr) -> ScmConst'(sexpr)
    | ScmVar'(var') -> ScmVar'(var')
    | ScmBox'(var') -> ScmBox'(var')
    | ScmBoxGet'(var') -> ScmBoxGet'(var')
    | ScmBoxSet'(var', expr') -> ScmBoxSet'(var', (run expr' false))
    | ScmIf'(expr1, expr2, expr3) -> ScmIf'((run expr1 false), (run expr2 in_tail), (run expr3 in_tail))
    | ScmSeq'(exprList) -> ScmSeq'((seqTail exprList in_tail))
    | ScmSet'(var', expr') -> ScmSet'(var',(run expr' false))
    | ScmDef'(var', expr') -> ScmDef'(var', (run expr' in_tail))
    | ScmOr'(exprList) -> ScmOr'((seqTail exprList in_tail))
    | ScmLambdaSimple'(stringList, expr') -> ScmLambdaSimple'(stringList, (run expr' true)) (* check if there is error*)
    | ScmLambdaOpt'(stringList, str, expr') -> ScmLambdaOpt'(stringList, str, (run expr' true))
    | ScmApplic'(op, exprList) -> (
        match in_tail with
            false -> ScmApplic'((run op false),((seqTail exprList false)))
          | true -> ScmApplicTP'((run op false),((seqTail exprList false))))
    | ScmApplicTP'(op,expList) -> ScmApplicTP'(op,expList)
   and seqTail tup in_tail =
    match tup with
      |[] -> []
      |list-> (match (rdc_rac list) with
        | (lst,item) -> (List.append (List.map (fun exp -> (run exp false)) lst) [(run item in_tail)]))
       in
   run pe false;;


  (* boxing *)
  (*let find_reads name enclosing_lambda expr = *)
  

  (* function that checks if there is Read/Write as parameter*)
  let checkIfVar name isRead isInner= 
    let rec runCheck isBound env expr = 
      (match expr with
     | ScmVar'(VarBound(str,minor,major)) -> if isBound then if isInner then if isRead then if (str = name) then [env] else [] else [] else [] else [] (*added check if its bound*)
     | ScmVar'(VarParam(str,integer)) -> if isBound then if isRead then if (str = name) then [env] else [] else [] else [] (*added check if its bound*)
     | ScmIf'(expr1,expr2,expr3) -> (runCheck isBound env expr1)@((runCheck isBound env expr2)@(runCheck isBound env expr3))
     | ScmSeq'(exprList) -> (List.fold_right List.append (List.map (fun exp -> (runCheck isBound env exp)) exprList) [])
     | ScmSet'(var', expr') -> if isRead then (runCheck isBound env expr') else 
          (match var' with
            VarBound(str,minor,major) -> if isInner then if (str = name) then [env] else [] else []
            |VarParam(str,integer) -> if isInner then [] else if (str = name) then [env] else []
            |_ -> [])
     | ScmDef'(var', expr') -> (runCheck isBound env expr')
     | ScmOr'(exprList) -> (List.fold_right List.append (List.map (fun exp -> (runCheck isBound env exp)) exprList) [])
     | ScmLambdaSimple'(stringList, expr') -> if (isInner && (not (List.mem name stringList))) then if isBound then (runCheck isBound env expr') else (runCheck true expr' expr') else []
     | ScmLambdaOpt'(stringList, str, expr') -> if (isInner && (not (List.mem name stringList)) && str!=name) then if isBound then (runCheck isBound env expr') else (runCheck true expr' expr') else []
     | ScmApplic'(expr', exprList) -> (List.append (runCheck isBound env expr') (List.fold_right List.append (List.map (fun exp -> (runCheck isBound env exp)) exprList) []))
     | ScmApplicTP'(expr', exprList) -> (List.append (runCheck isBound env expr') (List.fold_right List.append (List.map (fun exp -> (runCheck isBound env exp)) exprList) []))
     | _ -> []) in
   runCheck;;

   let replaceBox name = 
    let rec runCheck expr = 
      (match expr with
     | ScmVar'(VarParam(str,minor)) ->  if (str = name) then ScmBoxGet'(VarParam(str,minor)) else expr
     | ScmVar'(VarBound(str,minor,major)) ->  if (str = name) then ScmBoxGet'(VarBound(str,minor,major)) else expr
     | ScmIf'(expr1,expr2,expr3) -> ScmIf'((runCheck expr1),(runCheck expr2),(runCheck expr3))
     | ScmSeq'(exprList) -> ScmSeq'(List.map (fun exp -> (runCheck exp)) exprList)
     | ScmSet'(var', expr') -> 
      (match var' with
        | VarParam(str,minor) ->  if (str = name) then ScmBoxSet'(VarParam(str,minor),(runCheck expr')) else ScmSet'(var',(runCheck expr'))
        | VarBound(str,minor,major) ->  if (str = name) then ScmBoxSet'(VarBound(str,minor,major),(runCheck expr')) else ScmSet'(var',(runCheck expr'))
        | VarFree(str) -> ScmSet'(var', (runCheck expr')))
     | ScmDef'(var', expr') -> ScmDef'(var',(runCheck expr'))
     | ScmOr'(exprList) -> ScmOr'(List.map (fun exp -> (runCheck exp)) exprList)
     | ScmLambdaSimple'(stringList, expr') -> if (List.mem name stringList) then expr else ScmLambdaSimple'(stringList, (runCheck expr'))
     | ScmLambdaOpt'(stringList, str, expr') -> if (List.mem name (str::stringList)) then expr else ScmLambdaOpt'(stringList, str, (runCheck expr'))
     | ScmApplic'(expr', exprList) -> ScmApplic'((runCheck expr'), (List.map (fun exp -> (runCheck exp)) exprList)) 
     | ScmApplicTP'(expr', exprList) -> ScmApplicTP'((runCheck expr'), (List.map (fun exp -> (runCheck exp)) exprList))
     | exp -> exp) in
   runCheck;;

  let shouldBox env name body = 
    let readerChecker = (checkIfVar name true false) in
    let writerChecker = (checkIfVar name false false) in
    let readExists = (readerChecker true body body) in
    (* let a = Printf.printf "\n-----------------read-----------------------\n" in
    let a = Printf.printf "%B" (readExists!=[]) in  *)
    let writeExists = (writerChecker true body body) in
    (*let a = Printf.printf "\n-----------------write-----------------------\n" in
    let a = Printf.printf "%B" (writeExists!=[]) in *)
    let innerReads = ((checkIfVar name true true) false body body) in
    (*let a = Printf.printf "\n-----------------inner read-----------------------\n" in
    let a = Printf.printf "%B" (innerReads!=[]) in *)
    let innerWrites = ((checkIfVar name false true) false body body) in
    (* let a = Printf.printf "\n-----------------inner writes-----------------------\n" in
    let a = Printf.printf "%B" (innerWrites!=[]) in  *)
    let unique_innerReads = (remove_duplicates innerReads) in
    let unique_innerWrites = (remove_duplicates innerWrites) in
    let differentClosures = (ormap (fun x -> (ormap (fun y->x!=y) unique_innerWrites)) unique_innerReads) in
    (readExists!= [] && innerWrites != []) || (writeExists!=[] && innerReads != []) || differentClosures

  let rec find_index name index= function 
      | x::xs -> if x=name then index else (find_index name (index+1) xs)
      | [] -> -1;;

  let makeParamBox name newBody flag stringList = 
    let index = (find_index name 0 stringList) in
    if flag then
      (match newBody with
      | ScmSeq'(exprList) -> ScmSeq'(ScmSet'(VarParam(name, index),ScmBox'(VarParam(name,index)))::exprList)
      | seq -> ScmSeq'(ScmSet'(VarParam(name, index),ScmBox'(VarParam(name,index)))::[seq])) else newBody;;

  let makeSet stringList lambda body = 
    let shouldBoxArgs = (List.map (fun name -> (shouldBox lambda name body)) stringList) in
    let newBody1 = (List.fold_right2 (fun flag name body1 -> (makeParamBox name (if flag then (replaceBox name body1) else body1) flag stringList)) shouldBoxArgs stringList body) in
    newBody1;;  (*doesnt work together*)
    

  let rec box_set expr =  
    match expr with
    | ScmConst'(sexpr) -> ScmConst'(sexpr)
    | ScmVar'(var') -> ScmVar'(var')
    | ScmIf'(expr1, expr2, expr3) -> ScmIf'((box_set expr1), ( box_set expr2), (box_set expr3))
    | ScmSeq'(exprList) -> ScmSeq'((List.map box_set exprList))
    | ScmSet'(var', expr') -> ScmSet'(var', (box_set expr'))
    | ScmDef'(var', expr') -> ScmDef'(var', (box_set expr'))
    | ScmOr'(exprList) -> ScmOr'((List.map box_set exprList))
    | ScmLambdaSimple'(stringList, expr') -> ScmLambdaSimple'(stringList, (makeSet stringList expr (box_set expr')))
    | ScmLambdaOpt'(stringList, str, expr') -> ScmLambdaOpt'(stringList, str, (makeSet (str::stringList) expr (box_set expr')))
    | ScmApplic'(expr', exprList) -> ScmApplic'((box_set expr'), (List.map box_set exprList))
    | ScmApplicTP'(expr', exprList) -> ScmApplicTP'((box_set expr'), (List.map box_set exprList))
    | _ -> raise X_this_should_not_happen

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)



(*

*)