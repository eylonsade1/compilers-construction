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
 let rec ourPower nt n =
   if n = 0 then 1.0
   else if n > 0 then nt *. (ourPower nt (n-1))
   else (ourPower nt (n+1)) /. nt;;
 let rec list_to_proper =
  function
    | [] ->ScmNil
    | hd::tl -> ScmPair(hd, list_to_proper tl);;
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
   let nt_semicolon = char ';' in
   let nt_all_chars = unitify(range ' ' '~') in
   let nt_star_all_chars = unitify(star nt_all_chars) in
   let comment = caten (caten nt_semicolon nt_star_all_chars) nt_end_of_line_or_file in 
   (unitify comment) str
 and nt_paired_comment str = 
   let nt1 = char '{' in
   let nt2 = disj_list 
              [unitify nt_char; unitify nt_string; unitify nt_comment] in
    let nt22 = disj nt2 (unitify (one_of "{}")) in
    let nt3 = diff (unitify (nt_any)) nt22 in
    let nt3 = disj nt3 nt2 in
    let nt3 = star nt3 in
    let nt4 = char '}' in 
    let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
    nt1 str
 and nt_sexpr_comment str = 
   let nt_start = word "#;" in
   let nt1 = unitify (caten nt_start nt_sexpr) in
   nt1 str
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
   | _ -> raise X_no_match ) in
   packed str
 and nt_frac str = 
   let nt_slesh = char '/' in
   let nt1 = caten nt_int (caten nt_slesh nt_natural) in
   let packed = pack nt1 (fun (i, (s, n)) -> (i,n)) in
   let packed = only_if packed (fun (i,n)->not (n=0)) in
   let packed = pack packed (fun (i, n) -> ScmRational((i/(gcd i n)), (n/(gcd i n)))) in
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
   let packed = pack nt1 (fun (t,i) -> ourPower 10.0 i) in
   packed str
 and nt_float_A str = 
   let nt_dot = char '.' in
   let nt1 = caten nt_integer_part nt_dot in
   let nt2 = caten nt1 (maybe nt_mantissa) in
   let nt3 = caten nt2 (maybe nt_exponent) in
   let packed = pack nt3 (fun (((i, d), m), e) -> 
   match m, e with
   None, None -> float_of_int i 
   |Some(any1), None -> float_of_string((string_of_int i)^"."^(string_of_int any1)) 
   |None, Some(any2) -> float_of_int(i) *. any2 
   |Some(any3), Some(any4) -> float_of_string((string_of_int i)^"."^(string_of_int any3)) *. any4 ) in
   packed str
 and nt_float_B str = 
   let nt_dot = char '.' in
   let nt1 = caten nt_dot nt_mantissa in
   let nt2 = caten nt1 (maybe nt_exponent) in
   let packed = pack nt2 (fun ((d, m), e) -> 
   match e with
   None -> float_of_string("0."^(string_of_int m))
   |Some(exp) -> (float_of_string("0."^(string_of_int m))) *. exp) in
   packed str
 and nt_float_C str = 
   let nt1 = caten nt_integer_part nt_exponent in
   let packed = pack nt1 (fun (i, e) -> (float_of_int i) *. e) in
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
   | _ -> raise X_no_match ) in
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
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_char_simple str = 
   let nt1 = range '!' '~' in
   nt1 str
 and make_named_char char_name ch =   
   let nt1 = pack (word char_name) (fun _ -> ch) in
   nt1
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str
 and nt_char_hex str = 
   let chars = range 'a' 'f' in
   let nt1 = disj nt_digit chars in
   nt1 str
 and nt_hexa str =
  let hex_char =  caten (char 'x') (plus nt_char_hex) in
  let hex_packed = pack hex_char (fun (c,l) -> char_of_int(int_of_string("0x"^(list_to_string l)))) in
  hex_packed str
 and nt_char str = 
   let char_pref = word "#\\" in
   let nt1 = disj nt_char_named nt_hexa in
   let nt1 = disj nt1 nt_char_simple in
   let nt1 = caten char_pref nt1 in
   let packed = pack nt1 (fun (pref,c) -> ScmChar c) in
   let packed = not_followed_by packed nt_symbol_char in
   packed str
 and nt_symbol_char str = 
    let nt1 = range 'a' 'z' in
    let nt2 = disj nt1 (range 'A' 'Z') in
    let nt2 = disj nt2 (range '0' '9') in
    let nt3 = disj nt2 (char '!') in
    let nt4 = disj nt3 (char '$') in
    let nt4 = disj nt4 (char '^') in
    let nt4 = disj nt4 (char '*') in
    let nt4 = disj nt4 (char '-') in
    let nt4 = disj nt4 (char '_') in
    let nt4 = disj nt4 (char '=') in
    let nt4 = disj nt4 (char '+') in
    let nt4 = disj nt4 (char '<') in
    let nt4 = disj nt4 (char '>') in
    let nt4 = disj nt4 (char '?') in
    let nt4 = disj nt4 (char '/') in
    let nt4 = disj nt4 (char ':') in
    nt4 str
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str
 and nt_string_literal str =
   let nt1 = nt_any in
   let nt1 = diff nt1 (char '\\') in
   let nt1 = diff nt1 (char '\"') in
   let nt1 = diff nt1 (char '~') in
   nt1 str
 and nt_string_interpolated str = 
   let nt_start = word "~{" in
   let nt_end = word "}" in
   let nt1 = caten nt_start (caten nt_sexpr nt_end) in
   let packed = pack nt1 (fun (s, (sexp, e)) -> ScmPair ((ScmSymbol "format"), (ScmPair ((ScmString "~a"), ScmPair(sexp,ScmNil))))) in
   packed str
 and nt_string_meta str =
   let nt1 = pack (word "\\\\") (fun _ -> '\\') in
   let nt1 = disj nt1 (pack (word "\\\"") (fun _ -> '\"')) in
   let nt1 = disj nt1 (pack (word "\\t") (fun _ -> '\t')) in
   let nt1 = disj nt1 (pack (word "\\f") (fun _ -> '\012')) in
   let nt1 = disj nt1 (pack (word "\\n") (fun _ -> '\n')) in
   let nt1 = disj nt1 (pack (word "\\r") (fun _ -> '\r')) in
   let nt1 = disj nt1 (pack (word "~~") (fun _ -> '~')) in
   nt1 str
 and nt_string_hex_char str =
   let nt1 = word "\\x" in
   let nt2 = caten nt1 (plus nt_char_hex) in
   let nt2 = caten nt2 (word ";") in
   let packed = pack nt2 (fun ((bx,chex),semic) -> char_of_int(int_of_string("0x"^(list_to_string chex)))) in
   packed str
 and nt_string_char str = 
   let nt1 = disj nt_string_meta nt_string_hex_char in
   let nt1 = disj nt1 nt_string_literal in
   nt1 str
   
 and nt_static_string str = 
   let nt1 = plus nt_string_char in
   let packed = pack nt1 (fun st -> ScmString(list_to_string st)) in
   packed str
   
 and nt_string str = 
   let nt_geresh = word "\"" in
   let strng = star (disj nt_string_interpolated nt_static_string) in
   let packed = caten nt_geresh (caten strng nt_geresh) in
   let packed = pack packed (fun (g,(s,g1)) -> match (s) with
   [] -> ScmString("")
   | hd::[] -> hd
   | hd::tl -> list_to_proper([ScmSymbol "string-append"]@s)) in
   packed str
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
 and nt_proper_list str = 
   let nt1 = caten (char '(') nt_skip_star in
   let nt2 = caten nt_skip_star (char ')') in 
   let nt3 = star nt_sexpr in
   let nt4 = caten nt1 nt3 in
   let nt5 = caten nt4 nt2 in
   let packed = pack nt5 (fun ((poteach, s), soger)-> List.fold_right (fun a b -> ScmPair(a,b)) s ScmNil) in
   packed str
and nt_improper_list str = 
   let nt1 = caten (char '(') nt_skip_star in
   let nt2 = caten nt_skip_star (char ')') in 
   let nt_nekuda = caten nt_skip_star (caten (char '.') nt_skip_star) in
   let nt3 = star nt_sexpr in
   let nt4 = caten nt1 nt3 in
   let nt5 = caten nt4 nt_nekuda in
   let nt6 = caten nt5 nt_sexpr in 
   let nt7 = caten nt6 nt2 in
   let packed = pack nt7 (fun ((((poteah,s),nek),sexp),soger) -> List.fold_right (fun a b -> ScmPair(a,b)) s sexp) in
   packed str
 and nt_list str = 
   let nt1 = disj nt_proper_list nt_improper_list in
   nt1 str
 and nt_quoted str = 
   let nt_quote = char '\'' in
   let nt_quotes = caten nt_quote nt_sexpr in
   let packed = pack nt_quotes (fun (c, s) -> ScmPair(ScmSymbol("quote"), ScmPair(s, ScmNil))) in
   packed str
 and nt_quasi_quoted str = 
   let nt_quote = char '`' in
   let nt_quotes = caten nt_quote nt_sexpr in
   let packed = pack nt_quotes (fun (c, s) -> ScmPair(ScmSymbol("quasiquote"), ScmPair(s, ScmNil))) in
 packed str
 and nt_unquoted str = 
   let nt_quote = char ',' in
   let nt_quotes = caten nt_quote nt_sexpr in
   let packed = pack nt_quotes (fun (c, s) -> ScmPair(ScmSymbol("unquote"), ScmPair(s, ScmNil))) in
   packed str
 and nt_unquoted_and_splice str = 
   let nt_quote = word ",@" in
   let nt_quotes = caten nt_quote nt_sexpr in
   let packed = pack nt_quotes (fun (c, s) -> ScmPair(ScmSymbol("unquote-splicing"), ScmPair(s, ScmNil))) in
   packed str
 and nt_quoted_forms str = 
   let nt1 = disj nt_quoted nt_quasi_quoted in 
   let nt1 = disj nt1 nt_unquoted in 
   let nt1 = disj nt1 nt_unquoted_and_splice in
   nt1 str
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
