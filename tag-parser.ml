#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec checkDup = function
| [] -> false
| hd::tl -> ((List.mem hd tl) || (checkDup tl));;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec improper_to_list_without_last_arg = function
| ScmPair(ScmSymbol(hd), ScmPair(x,y)) -> hd::(improper_to_list_without_last_arg (ScmPair(x,y)))
| ScmPair(head, ScmNil) ->  raise (X_syntax_error (ScmPair(head, ScmNil) ,"unable to recognize improper list parse"))
| ScmPair(ScmSymbol(head),tail) -> (head::[])
| exep -> raise (X_syntax_error ( exep ,"unable to recognize improper list parse"));;

let rec improper_tail = function
| ScmPair(hd, ScmPair(x,y)) -> (improper_tail (ScmPair(x,y)))
| ScmPair(head, ScmNil) ->  raise (X_syntax_error (ScmPair(head, ScmNil) ,"unable to recognize improper list parse"))
| ScmPair(head,ScmSymbol(tail)) -> tail
| exep -> raise (X_syntax_error ( exep ,"unable to recognize improper list parse"));;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct



let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
  ScmNil -> ScmConst(ScmVoid)
| ScmBoolean(bool) -> ScmConst(ScmBoolean(bool))
| ScmChar(ch) -> ScmConst(ScmChar(ch))
| ScmNumber(x) -> ScmConst(ScmNumber(x))
| ScmString(s) -> ScmConst(ScmString(s))
| ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)) -> ScmConst(x)
| ScmSymbol(x) -> if(List.mem x reserved_word_list) then raise (X_reserved_word x)  else ScmVar(x) 
| ScmPair(ScmSymbol("if"),
          ScmPair(test,
                  ScmPair(dit,
                          ScmPair(dif,ScmNil)))) -> 
                              ScmIf((tag_parse_expression test),(tag_parse_expression dit),(tag_parse_expression dif))
| ScmPair(ScmSymbol("if"),
          ScmPair(test,
                  ScmPair(dit,ScmNil))) ->
                      ScmIf((tag_parse_expression test),(tag_parse_expression dit),ScmConst(ScmVoid))
| ScmPair(ScmSymbol("or"), x) -> (tag_parse_or x)
| ScmPair(ScmSymbol("lambda"),
          ScmPair(args,body)) -> 
          (match args with
          ScmNil -> ScmLambdaSimple([],(bodyParsing body))
          | ScmPair(_ ,_) -> 
            if (scm_is_list args)
              then 
                let argsStrings = (List.map (fun (ar) -> (sexpr_to_string ar)) (scm_list_to_list args)) in
                if (checkDup argsStrings) then (raise (X_syntax_error (sexpr, "lambda cannot have duplicate args"))) 
                else ScmLambdaSimple(argsStrings, (bodyParsing body))
              else 
                let argsStrings = (improper_to_list_without_last_arg args) in
                let tailString = (improper_tail args) in
                if(checkDup (tailString::argsStrings)) then (raise (X_syntax_error (sexpr, "lambda cannot have duplicate args"))) 
                else ScmLambdaOpt(argsStrings, tailString, (bodyParsing body))
          | ScmSymbol(sym) -> ScmLambdaOpt([], sym, (bodyParsing body))
          | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized")))
| ScmPair(ScmSymbol("define"), ScmPair(ScmSymbol(var), ScmPair(x , ScmNil))) -> ScmDef((tag_parse_expression (ScmSymbol(var))), (tag_parse_expression x))
| ScmPair(ScmSymbol("define"), ScmPair((ScmPair(ScmSymbol(funcName), args), body))) -> ScmDef((tag_parse_expression (ScmSymbol(funcName))), (tag_parse_expression (ScmPair(ScmSymbol("lambda"), ScmPair(args, body)))))
| ScmPair(ScmSymbol("set!"), ScmPair(ScmSymbol(var), ScmPair(value, ScmNil))) -> ScmSet((tag_parse_expression (ScmSymbol(var))),(tag_parse_expression value))(*add exeption of "Expected variable on LHS of set!"*)
| ScmPair(ScmSymbol("begin"), seqBody) -> (tag_parse_begin seqBody) 
(*| ScmPair(ScmPair(ScmSymbol("lambda"), body), argVal) -> ScmApplic((tag_parse_expression (ScmPair(ScmSymbol("lambda"), body)), (List.map tag_parse_expression (scm_list_to_list argVal))))*)
| ScmPair(funcName, rest) -> ScmApplic((tag_parse_expression funcName),(List.map tag_parse_expression (scm_list_to_list rest))) (*check parse func name *)
(* | ScmVector(lst) -> ScmConst(ScmVector(lst)) *)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized- main parse"))

and tag_parse_set = function
  | ScmPair(ScmSymbol(var), ScmPair(value, ScmNil)) -> ScmSet((tag_parse_expression (ScmSymbol(var))),(tag_parse_expression value))
  | body -> raise (X_syntax_error (body, "Expected variable on LHS of set!"))
  
and tag_parse_or = function
  | ScmNil -> ScmConst(ScmBoolean(false))
  | ScmPair(a, ScmNil) -> (tag_parse_expression a)
  | ScmPair(a, ScmPair(z)) -> ScmOr(List.map (fun y -> (tag_parse_expression y)) (scm_list_to_list (ScmPair(a, ScmPair(z))))) 
  | sexpr -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized- or"))

and tag_parse_begin = function 
  | ScmPair(body, ScmNil) -> (tag_parse_expression body)
  | body -> ScmSeq(List.map tag_parse_expression (scm_list_to_list body))

and sexpr_to_string = function
  | ScmSymbol(x) -> x
  | exp -> raise (X_syntax_error (exp, "Sexpr structure not recognized"))

and bodyParsing = function
    | ScmNil -> ScmConst(ScmVoid)
    | ScmPair(bodyArg,ScmNil) -> (tag_parse_expression bodyArg)
    | ScmPair(hd, tl) -> ScmSeq(List.map(fun listArg -> (tag_parse_expression listArg)) (scm_list_to_list (ScmPair(hd,tl))))
    | exp -> raise (X_syntax_error (exp, "problem with body parsing"))

and macro_expand sexpr =
match sexpr with
  ScmPair(ScmSymbol("and"), andBody) -> (expand_and_macro andBody)
| ScmPair(ScmSymbol("cond"), condBody) -> (macro_expand (expand_cond_macro condBody))
| ScmPair(ScmSymbol("let"), ScmPair(ribs, body)) -> ScmPair((ScmPair(ScmSymbol("lambda"), ScmPair((get_all_vars ribs) ,(macro_expand body)))), (get_all_values ribs)) 
| ScmPair(ScmSymbol("let*"), letStarBody) -> (macro_expand (expand_let_star_macro letStarBody))
| ScmPair(ScmSymbol("letrec"), letRecBody) -> (macro_expand (expand_letrec_macro letRecBody))
| ScmPair(ScmSymbol("quasiquote"), ScmPair(sexpr, ScmNil)) -> (expand_quasiquote_macro sexpr)
| _ -> sexpr

and expand_quasiquote_macro = function
| ScmPair(ScmSymbol("unquote"), ScmPair(sexpr, ScmNil)) -> (macro_expand sexpr)
| ScmPair(ScmSymbol("unquote-splicing"), sexpr) -> ScmPair(ScmSymbol("quote"),ScmPair(ScmPair(ScmSymbol("unquote-splicing"), sexpr), ScmNil)) 
| ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(ScmNil,ScmNil)) 
| ScmSymbol(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(x), ScmNil)) 
| ScmChar(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmChar(x), ScmNil)) 
| ScmString(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmString(x), ScmNil)) 
| ScmNumber(x) -> ScmNumber(x)
| ScmVector(x) -> ScmPair(ScmSymbol("list->vector"),ScmPair((expand_quasiquote_macro (list_to_proper_list x)), ScmNil)) 
| ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr,ScmNil)), b) -> ScmPair(ScmSymbol("append"), ScmPair(sexpr, ScmPair((expand_quasiquote_macro b,ScmNil))))
| ScmPair(a, ScmNil) -> ScmPair(ScmSymbol("cons"), ScmPair((expand_quasiquote_macro a),ScmPair((expand_quasiquote_macro ScmNil),ScmNil)))
| ScmPair(a, b) -> ScmPair(ScmSymbol("cons"), ScmPair((expand_quasiquote_macro a),ScmPair((expand_quasiquote_macro b),ScmNil)))
| sexpr -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized- quasiquote macro")) (*fix error *)



and expand_cond_macro = function
  | ScmNil -> ScmNil
  | ScmPair(ScmPair(ribTest, ScmPair(ScmSymbol("=>"), ribBody)), ribs) -> (
    let testBinding = ScmPair(ScmSymbol("value"), ScmPair(ribTest, ScmNil)) in
    let fBinding = ScmPair(ScmSymbol("f"), ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,ribBody)),ScmNil)) in
    let restFunc = ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ScmPair((expand_cond_macro ribs),ScmNil))) in
    let restBinding = ScmPair(ScmSymbol("rest"),ScmPair(restFunc, ScmNil)) in
    let dit = ScmPair(ScmPair(ScmSymbol("f"), ScmNil), ScmPair(ScmSymbol("value"), ScmNil)) in
    let dif = ScmPair(ScmSymbol("rest"), ScmNil) in
    let ifState = ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"), ScmPair(dit,ScmPair(dif,ScmNil)))) in
    ScmPair(ScmSymbol("let"), ScmPair(ScmPair(testBinding, ScmPair(fBinding, ScmPair(restBinding, ScmNil))),ScmPair(ifState, ScmNil)))
    )
    | ScmPair(ScmPair(ScmSymbol("else"), body), _) -> ScmPair(ScmSymbol("begin"), body)
    | ScmPair(ScmPair(ribTest, ribBody), ribs) -> ScmPair(ScmSymbol("if"), ScmPair(ribTest, ScmPair(ScmPair(ScmSymbol("begin"), ribBody), ScmPair((expand_cond_macro ribs), ScmNil))))
  | sexpr -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized- cond macro")) (*fix error *)


and expand_letrec_macro = function
  | ScmPair(ScmNil, body) -> (macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body))))
  | ScmPair(ribs, body) -> (
    let vars = (get_all_vars ribs) in
    let values = (get_all_values ribs) in 
    let demiVars = (scm_map (fun (var) -> ScmPair(var, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil)), ScmNil))) vars) in
    let setVars = (scm_zip (fun var value -> ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(value, ScmNil)))) vars values) in
    let appendBody = (scm_append setVars body) in
    let final = ScmPair(ScmSymbol("let"), ScmPair(demiVars, appendBody)) in
    (macro_expand final)
  )
  | sexpr -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized- letrec macro ")) (*fix error *)


and expand_let_star_macro = function
  | ScmPair(ScmNil, body) -> (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)))
  | ScmPair(ScmPair(rib, ScmNil), body) -> ScmPair( ScmSymbol("let"), ScmPair(ScmPair(rib, ScmNil), body))
  | ScmPair(ScmPair(rib, ribs), body) -> ScmPair( ScmSymbol("let"), ScmPair(ScmPair(rib, ScmNil), ScmPair((expand_let_star_macro (ScmPair(ribs, body)), ScmNil))))
  | sexpr -> raise (X_syntax_error (sexpr, "problem with  let star macro")) (*fix error *)

and expand_and_macro = function
    | ScmNil -> ScmBoolean(true)
    | ScmPair(a, ScmNil) -> a
    | ScmPair(a, ScmPair(z)) -> ScmPair(ScmSymbol("if"), ScmPair(a, ScmPair(macro_expand(ScmPair(ScmSymbol("and"), ScmPair(z))), ScmPair(ScmBoolean(false), ScmNil)))) 
    | sexpr -> raise (X_syntax_error (sexpr, "problem with expand and macro")) (*fix error *)
    
and get_all_vars = function
    | ScmNil -> ScmNil
    | ScmPair(ScmPair(var, _), ribs) -> ScmPair(var, (get_all_vars ribs))
    | sexpr -> raise (X_syntax_error (sexpr, "problem with get all vars")) (*fix error *)

and get_all_values = function
    | ScmNil -> ScmNil
    | ScmPair(ScmPair(_, ScmPair(value, ScmNil)), ribs) -> ScmPair(value, (get_all_values ribs))
    | sexpr -> raise (X_syntax_error (sexpr, "problem with get all values")) (*fix error *)


end;;
