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
    | ScmNumber(ScmRational(x, y)) -> 17
    | ScmNumber(ScmReal(x)) -> 9
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
    | [ScmBoolean(false), num] -> [ScmBoolean(false), (num, "db T_BOOL, 0")]
    | [ScmBoolean(true), num] -> [ScmBoolean(true), (num, "db T_BOOL, 1")]
    | [ScmChar(ch), num] -> [ScmChar(ch), (num, "MAKE_LITERAL_CHAR(" ^ (Char.escaped ch) ^ ")")]
    | [ScmNumber(ScmRational(x, y)), num] -> [ScmNumber(ScmRational(x, y)), (num, "MAKE_LITERAL_RATIONAL("^(Int.to_string x)^", "^(Int.to_string y)^")")] (*check*)
    | [ScmNumber(ScmReal(x)), num] -> [ScmNumber(ScmReal(x)), (num, "MAKE_LITERAL_FLOAT(" ^ (Float.to_string (x)) ^ ")")]
    | [ScmString(s), num] -> [ScmString(s), (num, "MAKE_LITERAL_STRING(\"" ^ s ^ "\")")]
    | [ScmPair(car, cdr), num] -> [ScmPair(car, cdr), (num, "MAKE_LITERAL_PAIR(const_tbl+" ^ (Int.to_string (find_offset car init)) ^ ", const_tbl+" ^ (Int.to_string (find_offset cdr init)) ^ ")")]
    | [ScmSymbol(x), num] -> [ScmSymbol(x), (num, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (Int.to_string (find_offset (ScmString(x)) init)) ^ ")")]
    | [ScmVector([]), num] -> [ScmVector([]), (num, "MAKE_LITERAL_VECTOR()")]
    | [ScmVector(list), num] ->  let str = (List.fold_left (fun initstr ex -> initstr ^ "const_tbl+" ^ (Int.to_string (find_offset ex init)) ^ ", ") "" list) in 
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
    let always_have = ["*";"+"; "-"; "/" ; "<" ; "=" ; ">";"append"; "apply"; "boolean?"; "car"; "cdr"; "char->integer"; "char?"; "cons"; "cons*"; "denominator"; "eq?"; "equal?"; "exact->inexact"; "flonum?"; "fold-left"; "fold-right"; "gcd"; "integer?"; "integer->char"; "length"; "list" ; "list?"; "make-string"; "map" ; "not"; "null?"; "number?"; "numerator"; "pair?"; "procedure?"; "rational?"; "set-car!"; "set-cdr!";"string->list"; "string-length"; "string-ref"; "string-set!"; "string?"; "symbol?"; "symbol->string";"zero?"] in
    let fvars = always_have @ fvars in
    let no_duplicates = (List.fold_left (fun init hd ->  if (List.mem hd init) then init else init @ [hd]) [] fvars) in
    let fvars_index = (List.fold_left (fun init ex -> init @ [((last_element init) + 1)]) [0] no_duplicates) in
    let fvars_index = (List.rev (List.tl (List.rev fvars_index))) in
    let fvars_with_index = (List.fold_left2 (fun init ex size -> init @ [(ex, size)]) [] no_duplicates fvars_index) in
    fvars_with_index
    ;;

  let make_counter () =
    let x = ref 0 in
    let get () = !x in
    let inc () = x := !x +1 in
    (get, inc);;

  let counter = make_counter();;

  let get_counter () = 
    begin
    (snd counter)();
    (Int.to_string ((fst counter)()))
    end;;

  let get_const_var c consts_tbl =
    let const_row = (List.find (fun (const,(_, _)) -> sexpr_eq const c) consts_tbl) in
    let offset = ((fun (_, (off, _)) -> off) const_row) in
    "mov rax, const_tbl+" ^ (Int.to_string offset) ^ "\n";;
 
  let find_index_in_tbl tbl name =
    let fvar = (List.find (fun (var, index) -> name = var) tbl) in
    (Int.to_string ((snd fvar)*8));;

  let get_Fvar name fvar_tbl =
    let index = (find_index_in_tbl fvar_tbl name) in
    "mov rax, qword [fvar_tbl+" ^ index ^ "]\n";;

  let set_Fvar var fvar_tbl = 
    let str = "mov qword [fvar_tbl+" ^ (find_index_in_tbl fvar_tbl var) ^ "], rax\n" in
    str ^ "mov rax, SOB_VOID_ADDRESS\n";;

  let set_var_param minor = 
    let str = "mov qword [rbp + 8 ∗ (4 + " ^ minor ^ ")], rax\n" in
    str ^ "mov rax, SOB_VOID_ADDRESS\n";;

  let get_bound_var minor major = 
    let str = "mov rbx, qword [rbp+16] ; rbx = env\n" in
    let str = str ^ "mov rcx, "^ major ^" ;rcx = major\n" in
    let str = str ^ "GET_N_ITEM rdx, rbx, rcx ; rdx = specific env\n" in
    let str = str ^ "mov rbx, " ^ minor ^ "; rbx = minor\n" in
    str ^ "GET_N_ITEM rax, rdx, rbx\n";;

  let set_bound_var minor major = 
    let str = "mov rbx, qword [rbp+8∗2]\n" in
    let str = str ^ "mov rbx, qword [rbx+8 ∗ " ^ major ^ "]\n" in 
    let str = str ^ "mov qword [rbx + 8 ∗ " ^ minor ^ "], rax\n" in
    str ^ "mov rax, SOB_VOID_ADDRESS\n";;
    
  let generate_or strList = 
    let index = (get_counter()) in
    let orStr = "cmp rax, SOB_FALSE_ADDRESS\njne Lexit" ^ index ^ "\n" in
    let ret = (List.fold_left (fun init str -> init ^ str ^ orStr) "" strList) in
    let ret = (String.sub ret 0 ((String.length ret) - (String.length orStr))) in 
    ret ^ "Lexit" ^ index ^ ":\n";;

  let generate_if test dit dif = 
    let index = (get_counter()) in 
    let str_test = test ^ "cmp rax, SOB_FALSE_ADDRESS\nje Lelse" ^ index ^ "\n" in 
    let str_dit = dit ^ "jmp Lexit" ^ index ^ "\nLelse" ^ index ^ ":\n" in
    let str_dif = dif ^ "Lexit" ^ index ^ ":\n" in
    str_test ^ str_dit ^ str_dif;;

  let generate_box_set expr var = 
    let str_expr = expr ^ "push rax\n" in
    let str_end = var ^ "pop qword [rax]\nmov rax, SOB_VOID_ADDRESS\n" in
    str_expr ^ str_end;;

let lambda_counter = make_counter ()

let generate_lambda_env stringList num_of_lambda body = 
  let env = "EXTAND_ENV_RCX\n" in
  let env = if num_of_lambda = 1 then "mov rcx, SOB_NIL_ADDRESS\n" else env in
  env
    
let generate_lambda_simple stringList num_of_lambda body =
    (*start generate env*)
    let env = generate_lambda_env stringList num_of_lambda body in
    (* end generate env*)
    (* allocate closure*)
    let make_closure = "MAKE_CLOSURE(rax, rcx, Lcode" ^ (Int.to_string num_of_lambda) ^ ")\n" in
    let closure_body = "jmp Lcont" ^ (Int.to_string num_of_lambda) ^ "\n" in
    let closure_body = closure_body ^ "Lcode" ^ (Int.to_string num_of_lambda) ^ ":\n" in
    let closure_body = closure_body ^ "push rbp\nmov rbp, rsp\n" in
    let closure_body = closure_body ^ body in
    let closure_body = closure_body ^ "leave\nret\nLcont" ^ (Int.to_string num_of_lambda) ^ ":\n" in
    (env ^ make_closure ^ closure_body);;

let generate_opt_last_arg num_of_args_without_opt counter = 
  let get_magic_pointer = "mov rcx, rbp\nadd rcx, 24\nmov rbx,qword [rcx]\nimul rbx, 8\nadd rcx, rbx\n" in
  (* let get_magic_pointer = get_magic_pointer ^ "lea rcx, [rbp+8*(3+rbx)]\n" in (*rcx stores pointer to magic*)*)
  let get_magic_pointer = get_magic_pointer ^ "mov rax, rcx\nsub rax, 8\n" in
  let get_last_non_opt_arg_index = "mov rdx, rbp\nadd rdx, "^(Int.to_string (8*(3+num_of_args_without_opt)))^"\n" in
  let generate_pair = "MAKE_LIST_LOOP" ^ (Int.to_string counter) ^ ":\n" in
  let generate_pair = generate_pair ^ "cmp rdx,rax\nje END_MAKE_LIST_LOOP" ^ (Int.to_string counter) ^ "\n" in
  let generate_pair = generate_pair ^ "push rax\nmov rax, qword [rax]\nmov rcx, qword [rcx]\n" in
  let generate_pair = generate_pair ^ "MAKE_PAIR(rbx, rax, rcx)\npop rax\nmov qword [rax], rbx\nmov rcx, rax\nsub rax, 8\n" in
  let generate_pair = generate_pair ^ "jmp MAKE_LIST_LOOP" ^ (Int.to_string counter) ^"\nEND_MAKE_LIST_LOOP" ^ (Int.to_string counter) ^":\n" in
  (get_magic_pointer ^ get_last_non_opt_arg_index ^ generate_pair)

let generate_lambda_opt stringList num_of_lambda body =
  let env = generate_lambda_env stringList num_of_lambda body in
  let make_closure = "MAKE_CLOSURE(rax, rcx, Lcode" ^ (Int.to_string num_of_lambda) ^ ")\n" in
  let closure_body = "jmp Lcont" ^ (Int.to_string num_of_lambda) ^ "\n" in
  let closure_body = closure_body ^ "Lcode" ^ (Int.to_string num_of_lambda) ^ ":\npush rbp\nmov rbp, rsp\n" in
  let num_of_args_without_opt = ((List.length stringList)) in
  let make_list_of_args = (generate_opt_last_arg num_of_args_without_opt num_of_lambda) in
  let closure_body2 = body ^ "leave\nret\nLcont" ^ (Int.to_string num_of_lambda) ^ ":\n" in
  (env ^ make_closure ^ closure_body ^ make_list_of_args ^ closure_body2);;

  let generate_applic arg_list proc =
    let make_args = (List.fold_right (fun arg init -> init ^ arg ^ "push rax\n") arg_list "push SOB_NIL_ADDRESS\n") in
    let push_n = "mov rax, rsp\nmov rax, 0x" ^ (Int.to_string ((List.length arg_list)+1)) ^ "\npush rax\n" in
    let call_proc = proc ^ "CLOSURE_ENV rbx, rax\n" in
    let call_proc = call_proc ^ "push rbx\n" in
    let call_proc = call_proc ^ "CLOSURE_CODE rbx, rax\n" in
    let call_proc = call_proc ^ "call rbx\n" in
    let finish_applic = "add rsp, 8 ; pop env\n
    pop rbx ; pop arg count\n
    lea rsp , [rsp + 8*rbx]\n" in
    (make_args ^ push_n ^ call_proc ^ finish_applic);;

  let generate_applicTP arg_list proc =
    let arg_count = (List.length arg_list) in
    let make_args = (List.fold_right (fun arg init -> init ^ arg ^ "push rax\n") arg_list "push SOB_NIL_ADDRESS\n") in
    let push_n = "push " ^ (Int.to_string (arg_count+1)) ^ "\n" in
    let get_closure = proc ^ "CLOSURE_ENV rbx, rax\n" in
    let get_closure = get_closure ^ "push rbx\n" in
    let save_ret_address = "push qword [rbp+8]\npush rax\n" in
    let fix_stack = "FIX_STACK\n" in
    let final_jump = "pop rax\nCLOSURE_CODE rbx, rax\n" in
    let final_jump = final_jump ^ "jmp rbx\n" in
    (make_args ^ push_n ^ get_closure ^ save_ret_address ^ fix_stack ^ final_jump);;
(*
    generate define == generate set
*)
  let rec generate_helper consts fvars lambda_counter = function
    | ScmConst'(sexpr) -> (get_const_var sexpr consts)
    | ScmVar'(VarFree(var)) -> (get_Fvar var fvars)
    | ScmVar'(VarParam(_, minor)) -> "mov rax, qword [rbp+"^(Int.to_string ((4+minor)*8))^"]\n"
    | ScmVar'(VarBound(_, major, minor)) -> (get_bound_var (Int.to_string minor) (Int.to_string major))
    | ScmBox'(var) -> "MALLOC rax, 8\n" (* check *)
    | ScmBoxGet'(var) -> (generate_helper consts fvars lambda_counter (ScmVar'(var))) ^ "mov rax, qword [rax]\n"
    | ScmBoxSet'(var, expr) -> (generate_box_set (generate_helper consts fvars lambda_counter expr) (generate_helper consts fvars lambda_counter (ScmVar'(var))))
    | ScmIf'(test, dit, dif) -> (generate_if (generate_helper consts fvars lambda_counter test) (generate_helper consts fvars lambda_counter dit) (generate_helper consts fvars lambda_counter dif))
    | ScmSeq'(exprList) -> (List.fold_left (fun init x -> init ^ (generate_helper consts fvars lambda_counter x)) "" exprList)
    | ScmSet'(VarParam(_, minor), expr) -> (generate_helper consts fvars lambda_counter expr) ^ (set_var_param (Int.to_string minor))
    | ScmSet'(VarBound(_, major, minor), expr) -> (generate_helper consts fvars lambda_counter expr) ^ (set_bound_var (Int.to_string minor) (Int.to_string major))
    | ScmSet'(VarFree(var), expr) -> (generate_helper consts fvars lambda_counter expr) ^ (set_Fvar var fvars)
    | ScmDef'(VarParam(var, minor), expr) -> (generate_helper consts fvars lambda_counter expr) ^ (set_Fvar var fvars) (* check *)
    | ScmDef'(VarBound(var, major, minor), expr) -> (generate_helper consts fvars lambda_counter expr) ^ (set_Fvar var fvars) (* check *)
    | ScmDef'(VarFree(var), expr) -> (generate_helper consts fvars lambda_counter expr) ^ (set_Fvar var fvars) (* check *)
    | ScmOr'(exprList) -> (generate_or (List.map (fun x -> generate_helper consts fvars lambda_counter x) exprList))
    | ScmLambdaSimple'(stringList, expr) -> (generate_lambda_simple stringList (lambda_counter()) (generate_helper consts fvars lambda_counter expr))
    | ScmLambdaOpt'(stringList, str, expr) -> (generate_lambda_opt stringList (lambda_counter()) (generate_helper consts fvars lambda_counter expr))
    | ScmApplic'(expr, exprList) -> (generate_applic (List.map (fun x -> generate_helper consts fvars lambda_counter x) exprList) (generate_helper consts fvars lambda_counter expr))
    | ScmApplicTP'(expr, exprList) -> (generate_applicTP (List.map (fun x -> generate_helper consts fvars lambda_counter x) exprList) (generate_helper consts fvars lambda_counter expr))
    ;;
  

  let generate consts fvars e =
   let lambda_counter = make_counter() in
    let get_lambda_counter () = 
      begin
      (snd lambda_counter)();
      (fst lambda_counter)()
      end in
    (generate_helper consts fvars get_lambda_counter e);;
end;;

