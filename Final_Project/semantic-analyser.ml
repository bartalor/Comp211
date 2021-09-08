#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;


let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
let first (x,_) = x
let second (_,x) = x

(* helper functions *)
  let position_in xs x =
    second (List.fold_left (fun acc cur -> 
    (((first acc) + 1) , (if ((cur = x) && ((second acc) = -1)) then ((first acc) + 1) else (second acc)))) (-1,-1) xs);;







  let list_expr' exp' =
    match exp' with | Seq'(x) -> x | _ -> [exp']
  (* list_expr' - greate done.*)



    
(* annotate lexical *)
  let create_lex x lst =
    let lex_addr xs x =
      (let minor_indexes = List.map (fun y -> position_in y x) xs in
      second (List.fold_left 
      (fun acc cur  -> (((first acc) + 1),
      (if (0 <= cur) && ((first (second acc)) = -1) then (((first acc) + 1),cur) else (second acc)))) (-1,(-1,-1)) minor_indexes)) in
    let x = (match x with | Var(x) -> x |_ -> raise X_syntax_error) in
    let maj, min = lex_addr lst x in
    if (maj = 0) then VarParam(x, min) else
    if (0 < maj) then VarBound(x, (maj-1), min) else 
    VarFree(x)


  (* create_lex - check again. *)
  let rec an_lex e lst =
    match e with 
    | Const(x) -> Const'(x)
    | If(test,dit,dif) -> If'(an_lex test lst, an_lex dit lst, an_lex dif lst)
    | Seq(xs) -> Seq'(List.map (fun exp -> an_lex exp lst) xs)
    | Set(var,valu) -> Set'(create_lex var lst , an_lex valu lst)
    | Def(var,valu) -> Def'(create_lex var lst , an_lex valu lst)
    | Var(x) -> Var'(create_lex e lst)
    | Or(xs) -> Or'(List.map (fun exp -> an_lex exp lst) xs) 
    | Applic(body , args) -> Applic'(an_lex body lst, List.map (fun arg -> an_lex arg lst) args)
    | LambdaSimple(params,body) -> LambdaSimple'(params , an_lex body (params::lst))
    | LambdaOpt(params , opt , body) -> LambdaOpt'(params, opt , an_lex body ((params@[opt])::lst))
  (* an_lex - great done. *)

(* annotate tail calls *)
  let rec an_tc exp is_tp =
    let is_last i xs =  (i == (List.length xs)-1) in
    match exp with 
    | Const'(x) -> Const'(x)
    | If'(test,dit,dif) -> If'(an_tc test false, an_tc dit is_tp, an_tc dif is_tp)
    | Or'(xs) -> Or'(List.mapi (fun i x -> an_tc x (is_tp && (is_last i xs))) xs)
    | Seq'(xs) -> Seq'(List.mapi (fun i x -> an_tc x (is_tp && (is_last i xs))) xs)
    | Set'(var,valu) -> Set'(var, an_tc valu false)
    | Def'(var,valu) -> Def'(var, an_tc valu false)
    | Var'(x) -> exp
    | LambdaSimple'(params, body) -> LambdaSimple'(params, an_tc body true)
    | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, an_tc body true)
    | Applic'(body, args) -> 
      if(is_tp) then 
        ApplicTP'(an_tc body false, List.map (fun arg -> an_tc arg false ) args)
      else 
        Applic'(an_tc body false, List.map (fun arg -> an_tc arg false ) args)
    | _ -> raise X_syntax_error;; 
  (* an_tc - great done. *) 

(* Boxing *)
  let rec var_occurence var depth env params = 
    match var with
    | VarParam(name,_) when (depth == 0) -> [name, params :: env]
    | VarBound(name,maj,_) when (depth == maj+1) -> [(name,params::env)]
    | _ -> [];;

  let rec is_param var = 
    match var with
    | VarParam(_) -> true
    | _ -> false;;

  let rec is_bound var = 
    match var with
    | VarBound(_) -> true
    | _ -> false;;

  let extract_var_name var =
    match var with
    | VarParam(name,_) | VarBound(name,_,_) | VarFree(name) -> name
  (* extract_var_name - great done. *)
  let var_in_occurence_list var lst = 
      List.mem (extract_var_name var) (List.map first lst)
  (* var_in_occurence_list - geat done.*)
  let append_tup (rlist1,wlist1) (rlist2,wlist2) =
    ((rlist1 @ rlist2),(wlist1 @ wlist2))
  let rec append_tup_list to_box =
    match to_box with 
    | [] -> ([],[])
    | car::cdr -> append_tup car (append_tup_list cdr)
  (* append_tup, tuplist - great done. *)
  let rec get_rw_occurences exp depth env cur_params rs ws opti = 
    let call obj  = get_rw_occurences obj depth env cur_params rs ws opti in
    match exp with
    | Const'(_)
    | BoxGet'(_)
    | Box'(_) -> ([],[])
    | If'(test,dit,dif) -> append_tup_list [call test; call dit; call dif]
    | Seq'(xs)
    | Or'(xs) -> append_tup_list (List.map call xs) 
    | LambdaSimple'(params,body) -> get_rw_occurences body (depth + 1) (cur_params :: env) params rs ws opti
    | LambdaOpt'(params, opt, body) -> get_rw_occurences body (depth + 1) (cur_params :: env) (params@[opt]) rs ws opti
    | Set'(var,valu) 
    | Def'(var,valu) -> append_tup (call valu)
                                    ([], 
                                    (if ((is_param var) && (var_in_occurence_list var ws)) || (not opti) || (is_bound var) then (var_occurence var depth env cur_params) else []))
    | Applic'(body,args)
    | ApplicTP'(body,args) -> append_tup_list (List.map call (body :: args))
    | Var'(var) -> 
      ((if (((is_param var) && (var_in_occurence_list var ws)) || (not opti) || (is_bound var)) then (var_occurence var depth env cur_params) else []),
      [])
    | BoxSet'(var,valu) -> call valu
  (* get_rw_occurences - great done. *)
  let get_rw_lists params body = 
      match body with
      | Seq'(xs) -> 
      (List.fold_left (fun acc x -> 
        (append_tup (get_rw_occurences x 0 [] params (first acc) (second acc) false) acc )) ([],[])  xs)
      | _ -> (get_rw_occurences body 0 [] params [] [] false)
  (* get_rw_lists - great done.*)
  let rec get_vars_that_should_be_box params body =
    let (reads,writes) = get_rw_lists params body in
    let should_box = fun (var1, lst1) -> 
    (List.exists (fun (var2, lst2) -> ((var1 = var2))) writes) in
    let to_box = List.map first (List.filter should_box reads) in
    List.filter (fun param -> (List.mem param to_box)) params

  let rec box var_name body =
    let call x = box var_name x in
    match body with
    Const'(_) | BoxGet'(_) | Box'(_) -> body
    | If'(test,dit,dif) ->  If'(call test, call dit, call dif)
    | LambdaSimple'(params,body) ->
      LambdaSimple'(params,
      if (List.mem var_name params) then body else (call body))
    | LambdaOpt'(params, opt, body) -> 
      LambdaOpt'(params, opt, 
      if (List.mem var_name (params@[opt])) then body else (call body))
    | Or'(xs) -> Or'(List.map call xs)
    | Set'(_,Box'(_)) -> body
    | Set'(var,valu) -> if ((extract_var_name var) = var_name) 
      then BoxSet'(var,call valu) else Set'(var,call valu)
    | Seq'(xs) -> Seq'(List.map call xs)
    | Def'(var,valu) -> Def'(var,call valu)
    | Applic'(body,args) -> Applic'(call body,List.map call args)
    | ApplicTP'(body,args) -> ApplicTP'(call body,List.map call args)
    | Var'(x) -> (
          match x with 
            VarParam(name,_) | VarBound(name,_,_) when (name = var_name) -> BoxGet'(x) 
            | _ -> body) 
    | BoxSet'(var,valu) -> BoxSet'(var,call valu) 
  (* box - great done.*)

  let box_body params body =
    if (params = []) then body else
    let vars_to_box = get_vars_that_should_be_box params body in 
    if (vars_to_box = []) then body else
    let sets = List.map (fun name ->
      let var = VarParam(name, position_in params name) in
      Set'(var, Box'(var))) vars_to_box in
    let new_body = Seq'(sets @ (list_expr' body)) in
    List.fold_left (fun acc var -> box var acc) new_body vars_to_box

  let rec an_box x =
    match x with
    | If'(test,dit,dif) -> If'(an_box test,an_box dit, an_box dif)
    | Var'(var) -> Var'(var)
    | Seq'(xs) -> Seq'(List.map an_box xs)
    | Const'(x) -> Const'(x)
    | Or'(xs) -> Or'(List.map an_box xs)
    | LambdaSimple'(params, body) -> LambdaSimple'(params,(box_body params (an_box body)))
    | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, (box_body (params@[opt]) (an_box body)))
    | Set'(var,valu) -> Set'(var, an_box valu)
    | Def'(var,valu) -> Def'(var, an_box valu)
    | ApplicTP'(body,args) -> ApplicTP'(an_box body, List.map an_box args)
    | Applic'(body, args) -> Applic'(an_box body, List.map an_box args)
    | _ -> raise X_no_match;;


module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;


module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = 
  an_lex e [];;


let annotate_tail_calls e = an_tc e false;;



let box_set e =  an_box e;; 


let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; 
