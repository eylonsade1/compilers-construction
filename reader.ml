(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;
 
 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 let nt_digit = range '0' '9';;
 let nt_natural = 
   let rec nt str = 
     pack (caten nt_digit
     (disj nt nt_epsilon)) (function (a,s) -> a::s) str in
     pack nt (fun s -> (fun a b -> 10 * a + b) 0  (int_of_string (list_to_string s)));;
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
 and nt_line_comment str =
   let nt_semicolon = unitify (char ';') in
   let nt_all_chars = range ' ' '~' in
   let nt_star_all_chars = unitify (star nt_all_chars) in
   let comment = caten (caten nt_semicolon nt_star_all_chars) nt_end_of_line_or_file in 
   let packed = pack comment (fun ((a,b),c) -> b) in
   packed str
 and nt_paired_comment str = raise X_not_yet_implemented
 and nt_sexpr_comment str = raise X_not_yet_implemented
 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1
 and nt_int str = 
   let plus = char '+' in
   let minus = char '-' in
   let nt_signs = disj plus minus in
   let nt1 = caten (maybe nt_signs) nt_natural in
   let packed = pack nt1 (fun (s,n) ->
   match s with
   None -> n
   |Some('+') -> n
   |Some('-') -> n*(-1)
   | _ -> n ) in (*check what to return*)
   packed str
 and nt_frac str = 
   let nt_slesh = char '/' in
   let nt1 = caten nt_int (caten nt_slesh nt_natural) in
   let packed = pack nt1 (fun (i, (s, n)) -> ScmRational(i/n,1)) in
   packed str
 and nt_integer_part str = 
   let nt1 = plus nt_digit in
   let packed = pack nt1 (fun s -> int_of_string(list_to_string s)) in
   packed str
 and nt_mantissa str = 
   let nt1 = plus nt_digit in
   let packed = pack nt1 (fun s -> int_of_string(list_to_string s)) in
   packed str
 and nt_exponent str = 
   let exponent_token = disj (word_ci "e") (disj (word "*10^") (word "*10**")) in
   let nt1 = caten exponent_token nt_int in
   let packed = pack nt1 (fun (t,i) -> ourPower 10 i) in
   packed str
 and nt_float_A str = raise X_not_yet_implemented
  (* let nt_dot = char '.' in
   let nt1 = caten nt_integer_part nt_dot in
   let nt2 = caten nt1 (maybe nt_mantissa) in
   let nt3 = caten nt2 (maybe nt_exponent) in
   let packed = pack nt3 (fun (((i, d), m), e) -> 
   match m, e with
   None, None -> float_of_int i 
   |_, None -> string_of_float((string_of_int i)^"."^(string_of_int m)) 
   |None, _ -> float_of_int(i *. e) 
   |_, _ -> string_of_float((string_of_int i)^"."^(string_of_int m)) *. e ) in
   packed str*)
 and nt_float_B str = raise X_not_yet_implemented
   (*let nt_dot = char '.' in
   let nt1 = caten nt_dot nt_mantissa in
   let nt2 = caten nt1 (maybe nt_exponent) in
   let packed = pack nt2 (fun ((d, m), e) -> 
   match e with
   None -> float_of_string("0."^(string_of_int m))
   |_ -> (float_of_string("0."^(string_of_int m))) *. e) in
   packed str*)
 and nt_float_C str = 
   let nt1 = caten nt_integer_part nt_mantissa in
   let packed = pack nt1 (fun (i, m) -> float_of_string((string_of_int i)^(string_of_int m))) in
   packed str
 and nt_float str = 
   let plus = char '+' in
   let minus = char '-' in
   let nt_signs = disj plus minus in
   let nt_floats = disj nt_float_A (disj nt_float_B nt_float_C) in 
   let nt1 = caten (maybe nt_signs) nt_floats in 
   let packed = pack nt1 (fun (s,f) ->
   match s with
   None -> ScmReal f
   |Some('+') -> ScmReal f
   |Some('-') -> ScmReal(f*.(-1.0))
   | _ -> ScmReal f ) in (*check what to return*) 
   packed str
 and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str = 
   let nt1 = pack (word_ci "#f") (fun _ -> false) in
   let nt2 = pack (word_ci "#t") (fun _ -> true) in
   let nt1 = disj nt1 nt2 in
   let nt1 = pack nt1 (fun r -> ScmBoolean r) in
   let nt1 = not_followed_by nt1 nt_symbol in
   nt1 str
 and nt_char_simple str = range '!' '~'
 and make_named_char char_name ch = raise X_not_yet_implemented
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str
 and nt_char_hex str = raise X_not_yet_implemented
 and nt_char str = raise X_not_yet_implemented
 and nt_symbol_char str = raise X_not_yet_implemented
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str
 and nt_string str = raise X_not_yet_implemented
 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str
 and nt_list str = raise X_not_yet_implemented
 and nt_quoted_forms str = raise X_not_yet_implemented
 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;
 