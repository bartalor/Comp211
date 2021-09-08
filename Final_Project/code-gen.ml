#use "semantic-analyser.ml";;

module type CODE_GEN = sig

  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  val make_fvars_tbl : expr' list -> (string * int) list

  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;
(* helper functions: *)
  let word_size = 8;;
  let first (x,_) = x
  let mapr f lst = List.fold_right (fun cur acc -> ((f cur)::acc)) lst ([]);;
  let rev_mapr f lst = List.rev (mapr f lst);;
  let concat_map f lst = List.concat (List.map f lst);;
  let mycall f (args: string list) = 
    let n = string_of_int(List.length args) in
    let pushes = List.rev_map (fun x -> "push "^x) args in
    let the_call = "call " ^ f in
    let pull_back = "add rsp, WORD_SIZE*"^n in
    String.concat "\n" (pushes @ [the_call; pull_back;]);;
  let unique_elems lst =
    List.fold_left (fun acc cur -> acc @ (if (List.mem cur acc) then [] else [cur])) [] lst



  let include_special_chars s =
    String.concat ", "
    (List.map string_of_int
    (List.map (Char.code) (string_to_list s)));;


(* main functions: *)
  let get_index =
    let counter = ref 0 in
    fun () -> incr counter; string_of_int(!counter);; 
    


  


  let rec extract_consts expr =
    match expr with
    | If'(test,dit,dif) -> concat_map extract_consts [test; dit; dif]
    | LambdaSimple'(_,body)
    | LambdaOpt'(_, _, body) -> extract_consts body
    | Or'(xs) 
    | Seq'(xs) ->  concat_map extract_consts xs
    | Set'(_,valu)
    | Def'(_,valu)
    | BoxSet'(_,valu) -> extract_consts valu
    | Applic'(body,args)
    | ApplicTP'(body,args) -> concat_map extract_consts (body::args)
    | Const'(Sexpr(x)) -> [x]
    | Const'(_)
    | Var'(_)
    | BoxGet'(_)
    | Box'(_) -> [] ;;

    

  let extend_consts_list lst = 
    let rec expand_const x = 
      (match x with
      | Pair(car,cdr) -> (concat_map expand_const [car;cdr])
      | Symbol(y) -> [Sexpr(String(y))]
      | _ -> []) 
      @ [Sexpr(x)] in
    concat_map expand_const lst;;
    
    let get_fvar name fvr_tbl =
    "fvar_tbl+" ^ (string_of_int (List.assoc name fvr_tbl))

  let get_const const const_tbl =
    "const_tbl + " ^ (string_of_int (first (List.assoc const const_tbl)));;
  
  let get_param min = 
    "PVAR(" ^ (string_of_int min) ^ ")";;

  let construct_consts_tbl consts =
    let const_to_lst_obj const cur_tbl cur_off=
      let make_lst_obj len str = (cur_off+len, (const,(cur_off,(str^"\n")))) in
      match const with 
      | Sexpr(Nil) -> make_lst_obj 1 "MAKE_NIL"
      | Void -> make_lst_obj 1 "MAKE_VOID"
      | Sexpr(Bool(true)) -> make_lst_obj 2 "MAKE_LITERAL_BOOL(1)"
      | Sexpr(Bool(false)) -> make_lst_obj 2 "MAKE_LITERAL_BOOL(0)"
      | Sexpr(Number(Fraction(a,b))) -> make_lst_obj 17  ("MAKE_LITERAL_RATIONAL(" ^ (string_of_int a) ^ ", " ^ (string_of_int b) ^ ")")
      | Sexpr(Number(Float(x))) -> make_lst_obj 9 ("MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^ ")")
      | Sexpr(Char(x)) -> make_lst_obj 2 ("MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code x)) ^ ")")
      | Sexpr(String("")) -> make_lst_obj 9  ("MAKE_LITERAL_STRING  \"\"") 
      | Sexpr(String(x)) -> make_lst_obj (9 + (String.length x)) ("MAKE_LITERAL_STRING  " ^ (include_special_chars x)) 
      | Sexpr(Symbol(x)) -> make_lst_obj 9 ("MAKE_LITERAL_SYMBOL(" ^ (get_const (Sexpr(String(x))) cur_tbl) ^ ")")
      | Sexpr(Pair(a,b)) -> make_lst_obj 17 ("MAKE_LITERAL_PAIR(" ^ (get_const (Sexpr(a)) cur_tbl) ^ ", " ^ (get_const (Sexpr(b)) cur_tbl) ^ ")")
      in
      
    first (List.fold_left (fun acc cur -> (
      let (off, obj) = (const_to_lst_obj cur (first acc) (second acc)) in
      (((first acc) @ [obj]), off))) ([],0) consts);;
      
  let rec extract_fvars expr =
      match expr with
      | If'(test,dit,dif) -> concat_map extract_fvars [test;dit;dif]
      | Or'(xs)
      | Seq'(xs) -> concat_map extract_fvars xs
      | BoxGet'(var) 
      | Box'(var) -> extract_fvars (Var'(var))
      | Set'(var,valu)
      | BoxSet'(var,valu)
      | Def'(var,valu) -> concat_map extract_fvars [Var'(var);valu]
      | LambdaSimple'(_, body)
      | LambdaOpt'(_, _, body) -> extract_fvars body
      | Applic'(body,args) 
      | ApplicTP'(body,args) -> concat_map extract_fvars (body::args)
      | Var'(VarFree(name)) -> [name]
      | Var'(_) 
      | Const'(_) -> [] ;;
  
  let rec construct_fvars_tbl fvars = 
        List.mapi (fun i x -> (x, i*word_size)) fvars

    

  let rec generate_exp consts fvars e depth = 
    let shrt x =  generate_exp consts fvars x depth in
    let shrt_lam x = generate_exp consts fvars x (depth+1) in
    let generate_or xs = 
      (let i = get_index ()  in
        String.concat "\n" (List.map (fun x -> (shrt x) ^
        "cmp rax, SOB_FALSE_ADDRESS\n" ^ 
        "jne exit_or" ^ i ^ "\n") 
        xs) ^ "exit_or" ^ i ^":\n") in

    let generate_if test dit dif=
      (let i = get_index () in
      ((shrt test) ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^ 
      "je ldif" ^ i ^ "\n" ^
      (shrt dit) ^ "jmp exit_if" ^ i ^ "\n" ^
      "ldif" ^ i ^ ":\n" ^
      (shrt dif) ^
      "exit_if" ^ i ^ ":\n")) in

    let generate_def valu name =
      ((shrt valu) ^
      "mov [" ^ (get_fvar name fvars) ^"], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n") in

    let generate_box min =
      ("mov rax, " ^ (get_param min) ^ "\n" ^
      (mycall "cons" ["SOB_NIL_ADDRESS"; "2"; "rax"; "SOB_NIL_ADDRESS";]) ^ "\n" ^
      "mov " ^ (get_param min) ^ ",rax\n") in

  
    let generate_boxset var valu = 
      ((shrt valu) ^
      "push rax\n" ^
      (shrt (Var'(var))) ^
      "pop rbx\n" ^
      (mycall "set_car" (["SOB_NIL_ADDRESS"; "2"; "rax"; "rbx";])) ^ "\n") in
    
    let make_env = 
      "
      ; copy bounds:
      MALLOC rax, WORD_SIZE * ("^ (string_of_int depth) ^" + 1) 			
      mov rbx,CUR_ARGC							
      shl rbx,3
      MALLOC rcx, rbx					
      mov [rax],rcx																
      mov rsi, CUR_ENV 
      lea rdi, FROM(rax,1)	
      CLD
      mov rcx, " ^ (string_of_int depth) ^"
      rep movsq
    
      ; copy params:
      mov rcx, CUR_ARGC
      lea rsi, PVAR(0)
      mov rdi, [rax]									
      rep	movsq	
      " in

    let fix_OPT params_N i= 
      "mov rax, "^ params_N ^"
      cmp ARGC_BEFORE_PUSH_RBP, rax										
      jae too_many_args" ^ i ^"
      too_few_args" ^ i ^":						
        mov rcx, ARGC_BEFORE_PUSH_RBP						
        add rcx, 3								
        push SOB_NIL_ADDRESS					
        lea rsi, FROM(rsp,1)
        mov rdi, rsp
        cld
        rep	movsq
        mov qword FROM(rsp,(2+"^ params_N ^")), SOB_NIL_ADDRESS					
        mov qword ARGC_BEFORE_PUSH_RBP, "^ params_N ^"
        jmp exit_fix_opt" ^ i ^"						
      too_many_args" ^ i ^ ":
      mov rbx, ARGC_BEFORE_PUSH_RBP								
      mov rcx, SOB_NIL_ADDRESS
      START_OF_ARGS_BEFORE_PUSH_RBP r8		
      build_arg_list" ^ i ^ ":
        cmp r8,(2+"^ params_N ^")						
        jb exit_build_arg_list" ^ i ^"			
        mov r9, FROM(rsp,r8)				
        MAKE_PAIR(rax,r9,rcx)	
        mov rcx,rax
        dec r8
        jmp build_arg_list" ^ i ^"
      exit_build_arg_list" ^ i ^":
      mov FROM(rsp,(2+" ^ params_N ^")),rcx					
      mov rsi,2+" ^ params_N ^"
      lea rdi, [rsi+(rbx-" ^ params_N ^")]
      lea rsi, FROM(rsp,rsi)
      lea rdi, FROM(rsp,rdi)
      lea rcx, FROM(rsp,(-2))
      std
      push_stack" ^ i ^":
        cmp rsi,rcx			     		
        je exit_push_stack" ^ i ^"				
        movsq							
        jmp push_stack" ^ i ^"
      exit_push_stack" ^ i ^":
      lea rsp, FROM(rsp,(rbx-" ^ params_N ^"))								
      mov qword ARGC_BEFORE_PUSH_RBP," ^ params_N ^"						
      exit_fix_opt" ^ i ^":
      " in


    let generate_lambda params_N body isOpt =
      (let i = get_index () in
      make_env ^ "\n" ^ 
      "mov rbx, rax\n" ^
      "MAKE_CLOSURE(rax, rbx, Lcode" ^ i ^ ")\n"^
      "jmp Lcont" ^ i ^ "\n" ^
      "Lcode" ^ i ^ ":\n" ^
      (if isOpt then ((fix_OPT (string_of_int params_N) i) ^ "\n") else "") ^
      "push rbp\n" ^
      "mov rbp, rsp\n" ^
      (shrt_lam body) ^
      "leave\n" ^
      "ret\n" ^
      "Lcont" ^ i ^ ":\n") in


      
      
    let generate_applic body args = 
      ((String.concat "\n" (rev_mapr (fun x-> (shrt x) ^ "push rax")  args)) ^ "\n" ^
      "push " ^ (string_of_int (List.length args)) ^ "\n" ^
      (shrt body) ^
      "CLOSURE_ENV rcx, rax\n" ^
      "CLOSURE_CODE rbx, rax\n" ^
      "push rcx\n" ^
      "call rbx\n" ^
      "add rsp,WORD_SIZE;  \n" ^
      "pop rcx     \n" ^
      "lea rsp, FROM(rsp,rcx) \n") in


    let fix_TP args_N = 
      "mov rbx,[rbp]								
      mov r9, CUR_ARGC
      add r9, 4 
      lea rdi, FROM(rbp,(r9-1))	
      lea rsi, FROM(rbp,(-1))		 
      mov rcx, 3+"^ args_N ^"									
      std
      rep movsq
      lea rsp,FROM(rbp,(r9-(3+" ^ args_N ^ ")))
      mov rbp,rbx" in
    
    let generate_applicTP body args =
      ((String.concat "\n" (rev_mapr (fun x-> (shrt x) ^ "push rax")  args)) ^ "\n" ^
      "push " ^ (string_of_int (List.length args)) ^ "\n" ^
      (shrt body) ^
      "CLOSURE_ENV rbx, rax\n" ^
      "push rbx\n" ^
      "push qword FROM(rbp,1)\n" ^
      "CLOSURE_CODE rax, rax\n" ^
      fix_TP(string_of_int (List.length args)) ^ "\n" ^
      "jmp rax\n" ) in
      

    let generate_boxget var = 
      (shrt (Var'(var))) ^
      (mycall "car" ["SOB_NIL_ADDRESS";"1";"rax";]) ^ "\n" in
      

    let generate_var var = 
      match var with
      | VarParam(_,min) -> "mov rax, " ^ (get_param min) ^ "\n"
      | VarBound(_,maj,min) -> "mov rax, CUR_ENV
                mov rax, FROM(rax, " ^ (string_of_int maj) ^ ")
                mov rax, FROM(rax, " ^ (string_of_int min) ^ ")\n"
      | VarFree(name) -> "mov rax, [" ^ (get_fvar name fvars) ^"]\n" in

    
    let generate_set var valu = 
      (shrt valu) ^
      match var with
      | VarParam(_, min) ->  "mov " ^ (get_param min) ^ ", rax
                mov rax, SOB_VOID_ADDRESS\n"
      | VarBound(_,maj,min) -> "mov rbx, CUR_ENV\n
                mov rbx, FROM(rbx, "^(string_of_int maj)^ ")
                mov FROM(rbx," ^ (string_of_int min) ^"), rax
                mov rax, SOB_VOID_ADDRESS\n"
      | VarFree(name) -> "mov [" ^ (get_fvar name fvars) ^ "],rax
                mov rax,SOB_VOID_ADDRESS\n" in
        
    
    match e with 
      | Def'(VarFree(name), valu) ->  generate_def valu name
      | Const'(x) -> "mov rax," ^ (get_const x consts) ^ "\n"
      | Var'(x) -> generate_var x
      | Set'(var, valu) -> generate_set var valu
      | Seq'(xs) -> String.concat "" (List.map shrt xs) 
      | Or'(xs) -> generate_or xs
      | If'(test,dit,dif) -> generate_if test dit dif
      | Box'(VarParam(_,min)) -> generate_box min
      | BoxGet'(var) -> generate_boxget var
      | BoxSet'(var,valu) -> generate_boxset var valu 
      | LambdaSimple'(params,body) ->  generate_lambda (List.length params + 1) body false
      | LambdaOpt'(params,_, body) -> generate_lambda (List.length params + 1) body true
      | Applic'(body,args) -> generate_applic body args
      | ApplicTP'(body,args) -> generate_applicTP body args
      | x -> raise X_syntax_error



        let primitives =
          [
            (* Type queries  *)
            "boolean?"; "flonum?"; "rational?";
            "pair?"; "null?"; "char?"; "string?";
            "procedure?"; "symbol?";
            (* String procedures *)
            "string-length"; "string-ref"; "string-set!";
            "make-string"; "symbol->string";
            (* Type conversions *)
            "char->integer"; "integer->char"; "exact->inexact";
            (* Identity test *)
            "eq?";
            (* Arithmetic ops *)
            "+"; "*"; "/"; "="; "<";
            (* Additional rational numebr ops *)
            "numerator"; "denominator"; "gcd";
            (* you can add yours here *)
            "car"; "cdr"; "set-car!"; "set-cdr!"; "cons"; "apply"; 
          ]


  module Code_Gen : CODE_GEN = struct
    let make_consts_tbl asts =
      let basic_consts =  [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))] in
      let init_consts = unique_elems (concat_map extract_consts asts) in
      let extended_consts = unique_elems (basic_consts @ (extend_consts_list init_consts)) in
      construct_consts_tbl extended_consts;;
      
      
    let make_fvars_tbl asts = 
      let fvars = unique_elems ((concat_map extract_fvars asts) @ primitives) in
      construct_fvars_tbl fvars;;
      
    let generate consts fvars e = generate_exp consts fvars e 0;;
  end;;
