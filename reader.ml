
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;


(* our own helper functions and parser combinators: *)
let chars chrs = disj_list (List.map char chrs);;
let not_char ch1 = const (fun ch2 -> ch2 != ch1)
let not_chars chars = const (fun ch2 ->
  let temp = (List.map (fun ch1 -> (ch2 != ch1)) chars) in 
  (List.fold_left (&&) true temp));;
let words wrds = disj_list (List.map word wrds);;
let words_ci wrds = disj_list (List.map word_ci wrds);;
let make_paired nt_left nt_right nt =
  (let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt) ;; 
let tail (a,b) = b;;
(* end own helper functions and parser combinators: *)
module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let nt_line_comment = 
  let nt_line_comment_start = pack (char ';') (fun _ -> []) in
  let nt_line_comment_content =  star (not_char '\n') in
  let nt_end_of_line = pack (char '\n') (fun _ -> []) in
  let nt_line_comment_end = disj nt_end_of_line nt_end_of_input in
  pack (caten_list [nt_line_comment_start; nt_line_comment_content; nt_line_comment_end])
  (fun _ -> ' ');;
let nt_bool = 
  let nt_detect_bool = (words_ci ["#t"; "#f";]) in
  pack nt_detect_bool 
  (fun a -> (Bool((String.lowercase_ascii (list_to_string a)) = "#t")));;

let nt_char = 
  let nt_char_prfx = pack (word "#\\") (fun _ -> Nil) in
  let nt_reg_char_content = pack (const (fun ch -> ' ' < ch)) (fun ch -> Char(ch)) in
  let nt_named_char_content = 
    let named_char_list = [("nul", 0); ("tab", 9); ("newline", 10); ("page", 12); 
    ("return", 13); ("space", 32)] in
    let nt_named_char_template name valu = pack (word_ci name) (fun _ -> Char(char_of_int valu)) in 
    disj_list (List.map (fun (name, valu) -> (nt_named_char_template name valu)) named_char_list) in 
  pack (caten nt_char_prfx (disj nt_named_char_content nt_reg_char_content)) tail;;

let nt_number =
  let nt_digit = range '0' '9' in
  let nt_nat = plus nt_digit in
  let nt_nat_to_num = pack nt_nat
    (fun dig_list -> int_of_string(list_to_string dig_list)) in
  let nt_sign = disj (pack (chars ['+'; '-']) (fun ch -> [ch])) nt_epsilon in
  let nt_sign_to_num = pack nt_sign
        (fun sign -> (if sign = ['-'] then -1 else 1)) in
  let nt_int_to_num = pack (caten nt_sign_to_num nt_nat_to_num) 
    (fun (sign , num) -> sign * num) in
  let nt_int_to_sexp = pack nt_int_to_num  
    (fun (num) -> Number (Fraction(num, 1))) in
  let nt_fraction_to_sexp =
    let rec gcd a b =
      if b = 0 then a 
               else (gcd b (a mod b)) in 
    let create_fraction sign a b =
      (let cur_gcd  = gcd a b in
      Number(Fraction(sign * (a/cur_gcd),b/cur_gcd))) in
    pack (caten_list [nt_sign_to_num; nt_nat_to_num; pack (char '/') (fun _ -> 0); nt_nat_to_num])
    (fun lst -> match lst with 
    |[sign; a; _; b] -> (create_fraction sign a b) |_ -> raise X_no_match) in
  let nt_float = pack (caten_list [nt_sign; nt_nat; (word "."); nt_nat]) List.flatten in
  let nt_float_to_num = pack nt_float 
  (fun float_list -> float_of_string (list_to_string float_list)) in
  let nt_float_to_sexp = pack nt_float_to_num
  (fun flt -> Number(Float(flt))) in
  let nt_scientific_to_sexp = 
    pack (caten_list [disj nt_float_to_sexp nt_int_to_sexp;
          pack (char_ci 'e') (fun ch -> Nil); nt_int_to_sexp])
         (fun lst -> match lst with 
         |[Number(num_r); _; Number(Fraction(num_l, _))] -> 
          let num_r = (match num_r with |Fraction(num_r,_) -> float_of_int(num_r) 
          |Float(num_r) -> num_r) in
          Number(Float(num_r *. (10.0 ** float_of_int (num_l))))
         |_ -> raise X_no_match) in
  disj_list [nt_scientific_to_sexp; nt_float_to_sexp; nt_fraction_to_sexp; nt_int_to_sexp];;

let nt_string = 
  let nt_double_quote = pack (char '\"') (fun _ -> Nil) in
  let nt_string_content =
    (let nt_string_char =  
      (let nt_reg_char = not_chars ['\\'; '\"'] in
      let nt_meta_char = 
        (let nt_meta_char_prfx = (char '\\') in
        let meta_char_list = [('\\', 92);('\"', 34);('f', 12);('t', 9);('n', 10);('r', 13);] in
        let nt_meta_char_template ch valu = pack 
          (caten nt_meta_char_prfx  (char ch)) (fun (_,ch) -> char_of_int valu) in
        disj_list (List.map (fun (ch,valu) -> (nt_meta_char_template ch valu)) meta_char_list)) in
      disj nt_reg_char nt_meta_char) in
    pack (star nt_string_char) 
    (fun (ch_list) -> String(list_to_string ch_list))) in
  (make_paired nt_double_quote nt_double_quote nt_string_content)

let nt_symbol =
  let nt_letter = range_ci 'a' 'z' in 
  let nt_digit_char = range '0' '9' in
  let punct_list = ['.'; '!'; '$'; '^'; '*'; '-';
   '_'; '='; '+'; '<'; '>'; '/'; '?'; ':'] in
  let nt_punct = chars punct_list in
  let nt_ch_list = (plus (disj_list [nt_letter; nt_digit_char; nt_punct])) in
  pack nt_ch_list
  (fun ch_list -> 
    let case_dot = if ch_list = ['.'] then raise X_no_match else Nil in
    if (case_dot != Nil) then Nil else(* just to make use of case_dot var...*)
    let case_start_with_number () = (let (num, rest) = (nt_number ch_list) in
    if rest = [] then num else raise X_no_match) in
    try (case_start_with_number ()) with X_no_match -> 
      Symbol(list_to_string (List.map Char.lowercase_ascii ch_list)));;

let rec nt_sexp () = 
  let nt_sexp_content =  disj_list [nt_symbol; nt_bool; nt_number; nt_char; nt_string; 
                                    delayed nt_list; delayed nt_quote] in
  (make_paired (delayed nt_garbage_dispose) (delayed nt_garbage_dispose) nt_sexp_content)

and nt_quote () = 
  let nt_quote_template q name = pack (caten (pack (word q) (fun w -> name)) (delayed nt_sexp))
  (fun (name, sexp) -> Pair (Symbol (name), Pair (sexp, Nil))) in
  let quote_list = [("\'", "quote");("`", "quasiquote");
  (",", "unquote");(",@", "unquote-splicing")] in
  disj_list (List.map (fun (q, name) ->
  (nt_quote_template q name)) quote_list)

and nt_list () =
  let nt_lparen = pack (char '(') (fun _ -> Nil) in 
  let nt_rparen = pack (char ')') (fun _ -> Nil) in 
  let nt_empty_list = 
    pack (make_paired nt_lparen nt_rparen (delayed nt_garbage_dispose))
    (fun _ -> Nil) in
  let nt_non_empty_list = 
    let nt_list_lside = pack (caten nt_lparen (plus (delayed nt_sexp))) tail in
    let list_to_sexp = (function
    | (sexps, last) -> List.fold_right (fun cur acc -> Pair((cur, acc))) sexps last) in
    let nt_reg_list = pack (caten nt_list_lside nt_rparen) list_to_sexp in
    let nt_dotted_list = 
      (let nt_dot = pack (char '.') (fun _ -> Nil) in
      let nt_dotted_list_rside = 
        make_paired nt_dot nt_rparen (delayed nt_sexp) in
      pack (caten nt_list_lside nt_dotted_list_rside) list_to_sexp) in
    disj nt_reg_list nt_dotted_list in
  disj nt_empty_list nt_non_empty_list
and nt_sexp_comment () = 
  pack (caten (pack (word "#;") (fun _ -> Nil)) (delayed nt_sexp)) (fun _ -> ' ') 

and nt_garbage_dispose () =
  let garbage = disj_list [nt_whitespace; nt_line_comment; (delayed nt_sexp_comment)] in
  pack (star garbage) (fun _ -> Nil);;


let read_sexprs string = 
  let parsed = (star (delayed nt_sexp)) (string_to_list string) in
  match parsed with 
  | (res, []) -> res
  | _ -> raise X_no_match;;

end;; (* struct Reader *)