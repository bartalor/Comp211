#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant    
  | Var of string             
  | If of expr * expr * expr  
  | Seq of expr list  
  | Set of expr * expr        
  | Def of expr * expr         
  | Or of expr list             
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;  
  



let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error of string;;
exception X_im_here of sexpr;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;
   
(* sexp generation functions *)
  let make_let binds body = Pair(Symbol "let", Pair(binds,body));;
  let make_let_star binds body = Pair(Symbol "let*", Pair(binds,body));;
  let make_if test dit dif = Pair(Symbol "if",Pair(test, Pair(dit, dif)));;
  let make_quote x =  Pair(Symbol "quote", Pair(x, Nil));;
  let make_set vars vals = Pair(Symbol "set!", Pair(vars, Pair(vals, Nil)));;
  let make_begin seq = Pair(Symbol "begin",seq);;
  let make_cond x= Pair(Symbol "cond", x);;
  let make_lambda args body = Pair(Symbol "lambda", Pair(args, body));;
  let make_and x = Pair(Symbol "and", x);;
  let make_unquote_splicing x = Pair(Symbol "unquote-splicing",Pair(x, Nil));;
  let make_define vars vals = Pair(Symbol "define", Pair(vars, Pair(vals, Nil)));;

(* helper functions *)
  let is_reserved_word x = List.mem x reserved_word_list;;  
  let rec is_reg_pairs pr = 
    match pr with
    | Nil | Pair(_, Nil) -> true
    | Pair(_, Pair(a, b)) -> is_reg_pairs (Pair(a, b))
    | Pair (_) -> false
    | _ -> raise (X_syntax_error "is_reg_pairs");;
  (* is_reg_pairs - looks good. *)
  let flatten_seq lst = 
    List.fold_left (fun acc cur -> 
    List.append acc (match cur with | Seq(x) -> x | _ -> [cur])) [] lst;;
  (* flatten_seq - great done. *)
  let rec list_pairs prs=
    match prs with
    | Nil -> []
    | Pair(x,y) ->  
      x :: (match y with | Nil -> [] | Pair(_) -> (list_pairs y) | _ -> [y])
    | _ -> raise X_no_match;;
  (* list_pairs - great done. *)
  let rec pair_list_with_last lst last =
    match lst with 
    | [] -> last
    | car :: cdr -> Pair(car, pair_list_with_last cdr last);;
  (* pair_list_with_last - great done. *)
  let rec pair_list lst = pair_list_with_last lst Nil;;
  (* pair_list - great done. *)
  let rec bind_params_to_garbage lst =
    let mapped = (List.map
    (fun x -> Pair(x, Pair(make_quote (Symbol("whatever")), Nil)))
    lst) in pair_list mapped;;
  (* bind_params_to_garbage - great done. *)
  let rec cover_body_with_sets args vals body =
    let lst = List.map2 (fun x y -> make_set x y) args vals in 
    pair_list_with_last lst body
  (* cover_body_with_sets - great done.*)
  let rec list_and_map_pairs f prs  =
    let lst = list_pairs prs in
    (List.map f lst);;
  (* list_and_map_pairs - great done. *)
  let binds_to_lists binds =
    List.split (list_and_map_pairs 
    (fun x -> match x with | (Pair(Symbol(arg), Pair(valu, _))) -> 
    (Symbol(arg), valu) | _ -> raise (X_syntax_error "binds_to_lists")) binds) 
  (* binds_to_lists - great done. *)
  let extract_syms pr = 
    list_and_map_pairs 
    (fun a -> match a with | (Symbol(x)) -> x 
    | _ -> raise (X_syntax_error "extract_syms")) pr;;
  (* extract_syms - good. *)
  let last lst = 
    List.hd (List.rev lst);;
  (* last - great done. *)
  let without_last lst= 
    List.rev (List.tl (List.rev lst));;
  (* without_last - great done. *)


let rec tparse sexp = 
  match sexp with
  | Number _| Bool _| Char _
  | String _ -> Const(Sexpr(sexp))
  | Symbol(x) -> if (not (is_reserved_word(x))) then Var(x) else raise (X_syntax_error "symbol reserved")
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("if"),if_content) -> tparse_if(if_content)
  | Pair(Symbol("lambda"), Pair(args,body)) -> tparse_lambda args body
  | Pair(Symbol("or"), or_content) -> tparse_or or_content
  | Pair(Symbol("and"), and_content) -> tparse_and and_content
  | Pair(Symbol("set!"), Pair(vars, Pair(vals, Nil))) -> Set(tparse vars, tparse vals)
  | Pair(Symbol("pset!"), pset_content) -> tparse_pset pset_content
  | Pair(Symbol("define"), define_content) -> tparse_define define_content
  | Pair(Symbol("begin"),begin_content) -> tparse_begin begin_content
  | Pair(Symbol("quasiquote"),Pair(quasiquote_content, Nil)) -> tparse_quasiquote quasiquote_content 
  | Pair(Symbol("cond"), cond_content) -> tparse_cond cond_content
  | Pair(Symbol("let"),  Pair(binds,body)) -> tparse_let binds body
  | Pair(Symbol("let*"), Pair(binds,body)) -> tparse_let_star binds body
  | Pair(Symbol("letrec"), Pair(binds,body)) -> tparse_letrec binds body
  | Pair(x,y) -> Applic (tparse x, (list_and_map_pairs tparse y))
  | _ -> raise (X_syntax_error "main")
(* tparse - great done. *)
(* secondary tparse functions *)
  and tparse_if sexp = 
    match sexp with
    | Pair(test, Pair(dit, Pair(dif, Nil))) -> If(tparse test, tparse dit, tparse dif)
    | Pair(test, Pair(dit,Nil)) -> If(tparse test, tparse dit, Const(Void))
    | _ -> raise (X_syntax_error "if")
  (* tparse_if - great done.*)

  and tparse_begin sexp = 
    match sexp with 
    | Nil -> Const(Void)
    | sexps -> tparse_seq sexps
  (* tparse_begin - great done. *)
  
  and tparse_quasiquote xs = 
    match xs with
    | Nil | Symbol(_) -> tparse (make_quote xs)
    | Pair(Symbol("unquote"),Pair(x,Nil)) -> tparse x
    | Pair(Symbol("unquote-splicing"),Pair(x,Nil)) ->tparse (make_quote (make_unquote_splicing x))
    | Pair(Pair(Symbol("unquote-splicing"),Pair(x,Nil)),y) -> Applic(Var("append"),[tparse x ; tparse_quasiquote y] )
    | Pair(x,y) -> Applic(Var("cons"),(List.map tparse_quasiquote [x;y]))
    | x -> tparse (make_quote x)
  (* tparse_quasiquote - greate done. *)

  and tparse_define sexp = 
    match sexp with 
    | Pair(Pair(Symbol(name), args), body) ->
        tparse (make_define (Symbol(name)) (make_lambda args body))
    | Pair(vars, Pair(vals, Nil)) -> Def(tparse vars, tparse vals)
    | _ -> raise (X_syntax_error "define")
  (* tparse_define - great done. *)
  and tparse_or sexps = 
    match sexps with
    | Nil ->  Const(Sexpr(Bool(false)))
    | Pair(x, Nil) ->  tparse x
    | _ -> Or(list_and_map_pairs tparse sexps)
  (* tparse_or - great done. *) 
  and tparse_and sexp = 
    match sexp with 
    | Nil -> Const(Sexpr(Bool(true)))
    | Pair(x, Nil) -> tparse x
    | Pair(car,cdr) -> 
      tparse (make_if car (make_and cdr) (Pair(Bool(false),Nil)))
    | _ -> raise (X_syntax_error "and")
  (* tparse_and - great done. *)
  and tparse_lambda args body =
    match args with
      | Symbol(sym) -> LambdaOpt([], sym, tparse_seq body)
      | _ -> let syms = extract_syms args in
        if(is_reg_pairs args) then LambdaSimple(syms,tparse_seq body)
        else LambdaOpt(without_last syms, last syms, tparse_seq body)
  (* tparse_lambda - great done. *)
  and tparse_let binds body = 
    let (args,vals) = binds_to_lists binds in
    let args = extract_syms (pair_list args) in
    let vals = List.map tparse vals in
    let body = tparse_seq body in
    Applic(LambdaSimple(args,body) ,vals)
  (* tparse_let - great done. *)
  and tparse_cond sexp=
    let expand_arrow_cond case func rest =
      (let case_name = Symbol "value" in
      let fun_name = Symbol "f" in
      let fun_val = Pair (make_lambda Nil (Pair(func, Nil)), Nil) in
      let case_val = Pair (case, Nil) in
      let case_bind = Pair (case_name, case_val) in
      let fun_bind = Pair (fun_name, fun_val) in
      let case_applic = Pair (Pair (fun_name, Nil), Pair (case_name, Nil)) in
      let rest_name = Symbol "rest" in
      let rest_applic = Pair(Pair (rest_name, Nil), Nil) in
      let rest_val = Pair (make_lambda Nil (Pair(make_cond rest, Nil)), Nil) in
      let rest_bind = Pair (rest_name, rest_val) in
      match rest with
      | Nil ->  (make_let (Pair (case_bind, Pair (fun_bind, Nil))) 
      (Pair (make_if case_name case_applic Nil, Nil)))
      | _ ->  (make_let (Pair(case_bind, Pair(fun_bind, Pair(rest_bind, Nil))))
      (Pair(make_if case_name case_applic rest_applic, Nil)))) in
    tparse (match sexp with
    | Pair (Pair (case, Pair (Symbol "=>", Pair (case_fun, Nil))), nextCond) -> expand_arrow_cond case case_fun nextCond                    
    | Pair (Pair (Symbol "else", else_fun), _) -> (make_begin else_fun)
    | Pair (Pair (case, case_fun), Nil) -> (make_if case (make_begin case_fun) Nil)
    | Pair (Pair (case, case_fun),rest) -> (make_if case (make_begin case_fun) (Pair(make_cond rest, Nil)))
    | _ -> raise (X_syntax_error "cond"))
  (* tpare_cond - great done. *)
  

  and tparse_let_star binds body =
    tparse (match binds with 
    | Pair(a, Pair(b, c)) -> make_let (Pair(a, Nil)) (Pair(make_let_star (Pair(b, c)) body, Nil))
    | Nil | Pair(_) -> make_let binds body
    | _ -> raise (X_syntax_error "let_star"))
  (* tparse_let_star - great done. *)
  and tparse_pset binds = 
    let int_to_sym i = Symbol("&" ^ (string_of_int i)) in
    let (args, vals) = binds_to_lists binds in
    let let_binds = pair_list (List.mapi
     (fun i valu -> (Pair(int_to_sym i, Pair(valu, Nil)))) vals) in
    let set_binds = pair_list (List.mapi
     (fun i arg -> (make_set arg (int_to_sym i))) args) in
    tparse (make_let let_binds set_binds)
  (* tparse_pset - great done. *)
  and tparse_letrec binds body =
    let (args, vals) = binds_to_lists binds in
    tparse (make_let 
    (bind_params_to_garbage args) 
    (cover_body_with_sets args vals body))
  (* tparse_letrec - great done. *)
  and tparse_seq sexps = 
    let temp = (flatten_seq(list_and_map_pairs tparse sexps)) in 
    if (List.length temp = 1) then (List.hd temp) else (Seq(temp))
  (* tparse_seq - great done. *)



let tag_parse_expressions sexpr = List.map tparse sexpr

  
end;; (* struct Tag_Parser *)
