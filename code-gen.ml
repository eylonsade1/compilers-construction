#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
(*
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
*)

    (* 
      1. go over the Sexpr and collect all constants 
      2. add the 4 MUST-haves: void, nil, false, true
      3. expantion: 'ab -> "ab"
      4. remove duplicates from the collection of constants- leave the first copy of each one
      5. add the constants offset + the command in assembly (can be done with 2 pattern matching)

      ** CONSTANTS CAN BE ANY SOB EXCEPT FOR CLOSURES **

   *)
   (*   let rec run = function
        | [] -> []
        | expr :: tail -> (find_all_consts expr) :: (run tail) in
      run asts


      *)
  let rec find_all_consts = function
    | ScmConst'(sexpr) -> [sexpr]
    | ScmVar'(var) -> []
    | ScmBox'(var) -> []
    | ScmBoxGet'(var) -> []
    | ScmBoxSet'(var, expr) -> (find_all_consts expr)
    | ScmIf'(test, dit, dif) -> (find_all_consts test) @ (find_all_consts dit) @ (find_all_consts dif)
    | ScmSeq'(exprList) -> (List.fold_left (fun init ex -> init @ (find_all_consts ex)) [] exprList)
    | ScmSet'(var, expr) -> (find_all_consts expr)
    | ScmDef'(var, expr) -> (find_all_consts expr)
    | ScmOr'(exprList) -> (List.fold_left (fun init ex -> init @ (find_all_consts ex)) [] exprList)
    | ScmLambdaSimple'(stringList, expr) -> (find_all_consts expr)
    | ScmLambdaOpt'(stringList, str, expr) -> (find_all_consts expr)
    | ScmApplic'(expr, exprList) -> (find_all_consts expr) @ (List.fold_left (fun init ex -> init @ (find_all_consts ex)) [] exprList)
    | ScmApplicTP'(expr, exprList) -> (find_all_consts expr) @ (List.fold_left (fun init ex -> init @ (find_all_consts ex)) [] exprList);;

    let rec expand_consts expr = 
      match expr with
      | ScmVector(list) -> (List.fold_left (fun init ex -> init @ (expand_if_needed ex)) [] list)
      | ScmPair(car, cdr) -> (expand_if_needed car) @ (expand_if_needed cdr)
      | ScmSymbol(x) -> [ScmString(x)]
      | _ -> [] 
    
    and expand_if_needed = function
      | ScmNil -> [ScmNil]
      | ScmVoid -> [ScmVoid]
      | ScmBoolean(bool) -> [ScmBoolean(bool)]
      | ScmChar(ch) -> [ScmChar(ch)]
      | ScmNumber(x) -> [ScmNumber(x)]
      | ScmString(s) -> [ScmString(s)]
      | ScmPair(car, cdr) -> (expand_if_needed car) @ ((expand_if_needed cdr) @ [ScmPair(car, cdr)])
      | ScmSymbol(x) -> [ScmString(x)] 
      | ScmVector(list) -> (List.fold_left (fun init ex -> init @ (expand_if_needed ex)) [] list) @ [ScmVector(list)]
      ;;

  let pack_with_size = function
    | ScmNil -> 1
    | ScmVoid -> 1
    | ScmBoolean(bool) -> 2
    | ScmChar(ch) -> 2
    | ScmNumber(x) -> 9
    | ScmString(s) -> ((String.length s) + 9)
    | ScmPair(car, cdr) -> 17
    | ScmSymbol(x) -> 9
    | ScmVector(list) -> (9 + (8 * (List.length list)))
    ;;

  let find_offset ex init =     
    let same = (List.find (fun (hd, tl) -> hd = ex) init) in 
    match same with 
    | (a, (num, b)) -> num
    ;;

  let pack_with_strings ex init = 
    match ex with
    | [ScmNil, num] -> [ScmNil, (num, "db T_NIL")]
    | [ScmVoid, num] -> [ScmVoid, (num, "db T_VOID")]
    | [ScmBoolean(false), num] -> [ScmBoolean(false), (num, "db T_BOOL 0")]
    | [ScmBoolean(true), num] -> [ScmBoolean(true), (num, "db T_BOOL 1")]
    | [ScmChar(ch), num] -> [ScmChar(ch), (num, "MAKE_LITERAL_CHAR(" ^ (Char.escaped ch) ^ ")")]
    | [ScmNumber(ScmRational(x, y)), num] -> [ScmNumber(ScmRational(x, y)), (num, "MAKE_LITERAL_INT(" ^ (Float.to_string (Int.to_float(x)/.Int.to_float(y))) ^ ")")]
    | [ScmNumber(ScmReal(x)), num] -> [ScmNumber(ScmReal(x)), (num, "MAKE_LITERAL_FLOAT(" ^ (Float.to_string (x)) ^ ")")]
    | [ScmString(s), num] -> [ScmString(s), (num, "MAKE_LITERAL_STRING(\"" ^ s ^ "\")")]
    | [ScmPair(car, cdr), num] -> [ScmPair(car, cdr), (num, "MAKE_LITERAL_PAIR(consts+" ^ (Int.to_string (find_offset car init)) ^ ", consts+" ^ (Int.to_string (find_offset cdr init)) ^ ")")]
    | [ScmSymbol(x), num] -> [ScmSymbol(x), (num, "MAKE_LITERAL_SYMBOL(consts+" ^ (Int.to_string (find_offset (ScmString(x)) init)) ^ ")")]
    | [ScmVector([]), num] -> [ScmVector([]), (num, "MAKE_LITERAL_VECTOR()")]
    | [ScmVector(list), num] ->  let str = (List.fold_left (fun initstr ex -> initstr ^ "consts+" ^ (Int.to_string (find_offset ex init)) ^ ", ") "" list) in 
                                        let str = (String.sub str 0 ((String.length str) - 2)) in
                                          [ScmVector(list), (num, "MAKE_LITERAL_VECTOR(" ^ str ^ ")")]
    | _ -> raise X_not_yet_implemented;;
    
  let rec last_element = function
    | tl :: [] -> tl
    | hd :: tl -> (last_element tl)
    | [] -> raise X_not_yet_implemented;;
 
  let make_consts_tbl asts = 
    let consts_list = (List.fold_left (fun init ex -> init @ (find_all_consts ex)) [] asts) in 
    let opening_four = [ScmVoid; ScmNil; ScmBoolean(false); ScmBoolean(true)] in
    let consts_with_opening_four = opening_four @ consts_list in 
    let consts_expanded = (List.fold_left (fun init ex -> init @ ((expand_consts ex) @ [ex])) [] consts_with_opening_four) in 
    let consts_no_duplicates = (List.fold_left (fun init hd ->  if (List.mem hd init) then init else init @ [hd]) [] consts_expanded) in
    let size_list = (List.fold_left (fun init ex -> init @ [((last_element init) + (pack_with_size ex))]) [0] consts_no_duplicates) in
    let size_list = (List.rev (List.tl (List.rev size_list))) in
    let consts_with_size = (List.fold_left2 (fun init ex size -> init @ [[ex, size]]) [] consts_no_duplicates size_list) in
    let consts_tbl = (List.fold_left (fun init ex -> init @ (pack_with_strings ex init)) [] consts_with_size) in
    consts_tbl
    ;;
      (* 
      1. go over all expr' and collect all free vars (tagged by the semantic analyser)
      2. remove duplicates from the collection of constants- leave the first copy of each one
      3. convert to list (string, int)
   *)

  let rec find_free_vars = function
    | ScmConst'(sexpr) -> []
    | ScmVar'(var) -> []
    | ScmBox'(var) -> []
    | ScmBoxGet'(var) -> []
    | ScmBoxSet'(var, expr) -> (find_free_vars expr)
    | ScmIf'(test, dit, dif) -> (find_free_vars test) @ (find_free_vars dit) @ (find_free_vars dif)
    | ScmSeq'(exprList) -> (List.fold_left (fun init ex -> init @ (find_free_vars ex)) [] exprList)
    | ScmSet'(var, expr) -> (find_free_vars expr)
    | ScmDef'(VarFree(var), expr) -> [var]
    | ScmDef'(var, expr) -> (find_free_vars expr)
    | ScmOr'(exprList) -> (List.fold_left (fun init ex -> init @ (find_free_vars ex)) [] exprList)
    | ScmLambdaSimple'(stringList, expr) -> (find_free_vars expr)
    | ScmLambdaOpt'(stringList, str, expr) -> (find_free_vars expr)
    | ScmApplic'(expr, exprList) -> (find_free_vars expr) @ (List.fold_left (fun init ex -> init @ (find_free_vars ex)) [] exprList)
    | ScmApplicTP'(expr, exprList) -> (find_free_vars expr) @ (List.fold_left (fun init ex -> init @ (find_free_vars ex)) [] exprList);;

  let make_fvars_tbl asts =
    let fvars = (List.fold_left (fun init ex -> init @ (find_free_vars ex)) [] asts) in
    let no_duplicates = (List.fold_left (fun init hd ->  if (List.mem hd init) then init else init @ [hd]) [] fvars) in
    let fvars_index = (List.fold_left (fun init ex -> init @ [((last_element init) + 1)]) [0] no_duplicates) in
    let fvars_index = (List.rev (List.tl (List.rev fvars_index))) in
    let fvars_with_index = (List.fold_left2 (fun init ex size -> init @ [(ex, size)]) [] no_duplicates fvars_index) in
    fvars_with_index
    ;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

