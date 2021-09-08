
 module type PRIMS = sig
  val procs : string;;
end

module Prims : PRIMS = struct
  let make_routine label body =
    label ^ ":
       push rbp
       mov rbp, rsp 
       " ^ body ^ "
         pop rbp
         ret";;

  let return_boolean jcc body =
    body ^ "
      " ^ jcc ^ " .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:";;

  let return_boolean_eq = return_boolean "je";;
  
  let make_unary label body = make_routine label ("mov rsi, PVAR(0)\n\t" ^ body);;
  let make_binary label body = make_unary label ("mov rdi, PVAR(1)\n\t" ^ body);;
  let make_tertiary label body = make_binary label ("mov rdx, PVAR(2)\n\t" ^ body);;

  let type_queries =
    let queries_to_types = [
        "boolean", "T_BOOL"; "flonum", "T_FLOAT"; "rational", "T_RATIONAL"; "pair", "T_PAIR";
        "null", "T_NIL"; "char", "T_CHAR"; "string", "T_STRING"; "symbol", "T_SYMBOL";
        "procedure", "T_CLOSURE"
      ] in
    let single_query name type_tag =
      make_unary (name ^ "?")
        (return_boolean_eq ("mov sil, byte [rsi]\n\tcmp sil, " ^ type_tag)) in
    String.concat "\n\n" (List.map (fun (a, b) -> single_query a b) queries_to_types);;

  let inline_gcd =
    ".gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:";;

  let numeric_ops =
    let numeric_op name flt_body rat_body body_wrapper =      
      make_binary name
        (body_wrapper
           ("mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne ." ^ name ^ "_rat
             " ^ flt_body ^ "
             jmp .op_return
          ." ^ name ^ "_rat:
             " ^ rat_body ^ "
          .op_return:")) in      
    let arith_map = [
        "MAKE_RATIONAL(rax, rdx, rdi)
         mov PVAR(1), rax
         pop rbp
         jmp mul", "divsd", "div";
        
        "imul rsi, rdi
	 imul rcx, rdx", "mulsd", "mul";
        
        "imul rsi, rdx
	 imul rdi, rcx
	 add rsi, rdi
	 imul rcx, rdx", "addsd", "add";
      ] in
    let arith name flt_op rat_op =
      numeric_op name
        ("FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  " ^ flt_op ^ " xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)")
        ("DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          " ^ rat_op ^ "
	  mov rax, rcx
	  mov rdi, rsi
          " ^ inline_gcd ^ "
	  mov rdi, rax
	  mov rax, rsi
	  cqo
	  idiv rdi
	  mov rsi, rax
	  mov rax, rcx
	  cqo
	  idiv rdi
	  mov rcx, rax
          cmp rcx, 0
          jge .make_rat
          imul rsi, -1
          imul rcx, -1
          .make_rat:
          MAKE_RATIONAL(rax, rsi, rcx)") in
    let comp_map = [
        (* = *)
        return_boolean_eq,
        "NUMERATOR rcx, rsi
	 NUMERATOR rdx, rdi
	 cmp rcx, rdx
	 jne .false
	 DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 cmp rcx, rdx
         .false:",
        "FLOAT_VAL rsi, rsi
	 FLOAT_VAL rdi, rdi
	 cmp rsi, rdi", "eq";

        (* < *)
        return_boolean "jl",
        "DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 NUMERATOR rsi, rsi
	 NUMERATOR rdi, rdi
	 imul rsi, rdx
	 imul rdi, rcx
	 cmp rsi, rdi",
        "FLOAT_VAL rsi, rsi
	 movq xmm0, rsi
	 FLOAT_VAL rdi, rdi
	 movq xmm1, rdi
	 cmpltpd xmm0, xmm1
         movq rsi, xmm0
         cmp rsi, 0", "lt";
      ] in
    let comparator comp_wrapper name flt_body rat_body = numeric_op name flt_body rat_body comp_wrapper in
    (String.concat "\n\n" (List.map (fun (a, b, c) -> arith c b a (fun x -> x)) arith_map)) ^
      "\n\n" ^
        (String.concat "\n\n" (List.map (fun (a, b, c, d) -> comparator a d c b) comp_map));;


  let misc_ops =
    let misc_parts = [
        (* string ops *)
        "STRING_LENGTH rsi, rsi
         MAKE_RATIONAL(rax, rsi, 1)", make_unary, "string_length";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         mov sil, byte [rsi]
         MAKE_CHAR(rax, sil)", make_binary, "string_ref";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         CHAR_VAL rax, rdx
         mov byte [rsi], al
         mov rax, SOB_VOID_ADDRESS", make_tertiary, "string_set";
        
        "NUMERATOR rsi, rsi
         CHAR_VAL rdi, rdi
         and rdi, 255
         MAKE_STRING rax, rsi, dil", make_binary, "make_string";
        
        "SYMBOL_VAL rsi, rsi
	 STRING_LENGTH rcx, rsi
	 STRING_ELEMENTS rdi, rsi
	 push rcx
	 push rdi
	 mov dil, byte [rdi]
	 MAKE_CHAR(rax, dil)
	 push rax
	 MAKE_RATIONAL(rax, rcx, 1)
	 push rax
	 push 2
	 push SOB_NIL_ADDRESS
	 call make_string
	 add rsp, 4*8
	 STRING_ELEMENTS rsi, rax   
	 pop rdi
	 pop rcx
	 cmp rcx, 0
	 je .end
         .loop:
	 lea r8, [rdi+rcx]
	 lea r9, [rsi+rcx]
	 mov bl, byte [r8]
	 mov byte [r9], bl
	 loop .loop
         .end:", make_unary, "symbol_to_string";

        (* the identity predicate (i.e., address equality) *)
        (return_boolean_eq "cmp rsi, rdi"), make_binary, "eq?";

        (* type conversions *)
        "CHAR_VAL rsi, rsi
	 and rsi, 255
	 MAKE_RATIONAL(rax, rsi, 1)", make_unary, "char_to_integer";

        "NUMERATOR rsi, rsi
	 and rsi, 255
	 MAKE_CHAR(rax, sil)", make_unary, "integer_to_char";

        "DENOMINATOR rdi, rsi
	 NUMERATOR rsi, rsi 
	 cvtsi2sd xmm0, rsi
	 cvtsi2sd xmm1, rdi
	 divsd xmm0, xmm1
	 movq rsi, xmm0
	 MAKE_FLOAT(rax, rsi)", make_unary, "exact_to_inexact";

        "NUMERATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "numerator";

        "DENOMINATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "denominator";

        (* GCD *)
        "xor rdx, rdx
	 NUMERATOR rax, rsi
         NUMERATOR rdi, rdi
         " ^ inline_gcd ^ "
	 mov rdx, rax
         cmp rdx, 0
         jge .make_result
         neg rdx
         .make_result:
         MAKE_RATIONAL(rax, rdx, 1)", make_binary, "gcd";  
      ] in
    String.concat "\n\n" (List.map (fun (a, b, c) -> (b c a)) misc_parts);;

let additional_prims = 

  let start_func = 
    "
    push rbp
    mov rbp, rsp
    " in

  let end_func = 
    "
    pop rbp
    ret
    " in

  let cons = 
    "cons:" 
    ^ start_func ^ "
    mov r8, PVAR(0)          
    mov r9, PVAR(1)          
    MAKE_PAIR(rax, r8, r9)
    " ^ end_func in

  let car = 
    "car:" 
    ^ start_func ^ "
    mov r8,PVAR(0)       
    CAR rax,r8
    " ^ end_func in

  let cdr =         
    "cdr:"
    ^ start_func ^
    "
    mov r8, PVAR(0)      
    CDR rax, r8
    " ^ end_func
    in

  let set_car = 
    "set_car:"       
    ^ start_func ^ "
    mov r9, PVAR(0)         
    mov r8, PVAR(1)        
    mov [r9 + TYPE_SIZE], r8
    mov rax, SOB_VOID_ADDRESS
    " ^ end_func 
        in 

  let set_cdr = 
    "set_cdr: "
    ^ start_func ^ "
    mov r8, PVAR(0)         
    mov r9, PVAR(1)        
    mov [r8 + TYPE_SIZE + WORD_SIZE], r9
    mov rax, SOB_VOID_ADDRESS
    " ^ end_func  in 

  let apply_push_list =
    "mov rbx, CUR_ARGC
      mov rbx, PVAR((rbx-1)) 
      push_list:
        cmp rbx, SOB_NIL_ADDRESS
        je exit_push_list
        CAR rcx, rbx            
        push rcx
        CDR rbx, rbx             
        jmp push_list
        exit_push_list:" in 
    
  let reverse_list = 
    " lea r9, FROM(rbp,(-1))
      mov r8, rsp
      rev_list:
        cmp r8, r9
        jae exit_rev_list
        mov rbx, [r9]                  
        xchg rbx, [r8]
        mov [r9], rbx
        sub r9, WORD_SIZE
        add r8, WORD_SIZE
        jmp rev_list
      exit_rev_list: " in

    let push_rest_args  = 
      "mov rbx, CUR_ARGC     
      lea rcx, [rbx -2]              
      cmp rcx, 0
      je exit_push_rest_args
      push_rest_args:
        push qword PVAR(rcx)
        loop push_rest_args
      exit_push_rest_args:" in

    let call_the_function = 
      "mov rdx, rbp
      sub rdx, rsp
      shr rdx, 3 
      push rdx                    
      mov rbx, PVAR(0)        
      CLOSURE_ENV rcx, rbx
      push rcx
      CLOSURE_CODE rcx, rbx
      call rcx
      add rsp, WORD_SIZE
      pop rcx
      lea rsp, FROM(rsp, rcx)" in

    let apply =
      "apply:" ^
      start_func ^ 
      apply_push_list ^ "\n" ^ 
      reverse_list ^ "\n" ^   
      push_rest_args ^ "\n" ^
      call_the_function ^ "\n" ^
      end_func in 


   



    
    
      (cons ^ car ^ cdr ^ set_car ^ set_cdr ^ apply)


  let procs = String.concat "\n\n" [type_queries ; numeric_ops; misc_ops; additional_prims];;
end;;