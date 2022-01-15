;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include "compiler.s"

section .bss
;;; This pointer is used to manage allocations on our heap.
malloc_pointer:
    resq 1

;;; here we REServe enough Quad-words (64-bit "cells") for the free variables
;;; each free variable has 8 bytes reserved for a 64-bit pointer to its value
fvar_tbl:
    resq 48

section .data
const_tbl:
db T_VOID
db T_NIL
db T_BOOL, 0
db T_BOOL, 1
MAKE_LITERAL_RATIONAL(1, 1)
MAKE_LITERAL_RATIONAL(0, 1)
MAKE_LITERAL_RATIONAL(10, 1)
MAKE_LITERAL_RATIONAL(200, 1)
MAKE_LITERAL_STRING "whatever"
MAKE_LITERAL_SYMBOL(const_tbl+74)

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS const_tbl+0
%define SOB_NIL_ADDRESS const_tbl+1
%define SOB_FALSE_ADDRESS const_tbl+2
%define SOB_TRUE_ADDRESS const_tbl+4

global main
section .text
main:
    ;; set up the heap
    mov rdi, GB(2)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0                ; argument count
    push SOB_NIL_ADDRESS  ; lexical environment address
    push T_UNDEFINED      ; return address
    push rbp                    
    mov rbp, rsp                ; anchor the dummy frame

    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we simulate the missing (define ...) expressions
    ;; for all the primitive procedures.
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, boolean?)
mov [fvar_tbl+72], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, flonum?)
mov [fvar_tbl+160], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, rational?)
mov [fvar_tbl+296], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, pair?)
mov [fvar_tbl+280], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, null?)
mov [fvar_tbl+256], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, char?)
mov [fvar_tbl+104], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, string?)
mov [fvar_tbl+352], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, procedure?)
mov [fvar_tbl+288], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, symbol?)
mov [fvar_tbl+360], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, string_length)
mov [fvar_tbl+328], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, string_ref)
mov [fvar_tbl+336], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, string_set)
mov [fvar_tbl+344], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, make_string)
mov [fvar_tbl+232], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, symbol_to_string)
mov [fvar_tbl+368], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, char_to_integer)
mov [fvar_tbl+96], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, integer_to_char)
mov [fvar_tbl+200], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, exact_to_inexact)
mov [fvar_tbl+152], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, eq?)
mov [fvar_tbl+136], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, add)
mov [fvar_tbl+8], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, mul)
mov [fvar_tbl+0], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, div)
mov [fvar_tbl+24], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, eq)
mov [fvar_tbl+40], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, lt)
mov [fvar_tbl+32], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, numerator)
mov [fvar_tbl+272], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, denominator)
mov [fvar_tbl+128], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, gcd)
mov [fvar_tbl+184], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, car)
mov [fvar_tbl+80], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, cdr)
mov [fvar_tbl+88], rax
MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, cons)
mov [fvar_tbl+112], rax

user_code_fragment:
;;; The code you compiled will be added here.
;;; It will be executed immediately after the closures for 
;;; the primitive procedures are set up.
push SOB_NIL_ADDRESS
mov rax, const_tbl+91
push rax
mov rax, rsp
mov rax, 0x2
push rax
mov rcx, SOB_NIL_ADDRESS
MAKE_CLOSURE(rax, rcx, Lcode5)
jmp Lcont5
Lcode5:
push rbp
mov rbp, rsp
push SOB_NIL_ADDRESS
mov rax, const_tbl+57
push rax
mov rax, rsp
mov rax, 0x2
push rax
push SOB_NIL_ADDRESS
mov rax, const_tbl+40
push rax
mov rax, rsp
mov rax, 0x2
push rax
EXTAND_ENV_RCX
MAKE_CLOSURE(rax, rcx, Lcode4)
jmp Lcont4
Lcode4:
push rbp
mov rbp, rsp
EXTAND_ENV_RCX
MAKE_CLOSURE(rax, rcx, Lcode3)
jmp Lcont3
Lcode3:
push rbp
mov rbp, rsp
MALLOC rax, 8
mov qword [rbp+32], rax
mov rax, SOB_VOID_ADDRESS
push SOB_NIL_ADDRESS
EXTAND_ENV_RCX
MAKE_CLOSURE(rax, rcx, Lcode2)
jmp Lcont2
Lcode2:
push rbp
mov rbp, rsp
mov rax, const_tbl+23
push rax
mov rbx, qword [rbp+16] ; rbx = env
mov rcx, 0 ;rcx = major
GET_N_ITEM rdx, rbx, rcx ; rdx = specific env
mov rbx, 0; rbx = minor
GET_N_ITEM rax, rdx, rbx
pop qword [rax]
mov rax, SOB_VOID_ADDRESS
leave
ret
Lcont2:
push rax
EXTAND_ENV_RCX
MAKE_CLOSURE(rax, rcx, Lcode1)
jmp Lcont1
Lcode1:
push rbp
mov rbp, rsp
push SOB_NIL_ADDRESS
mov rax, const_tbl+6
push rax
mov rbx, qword [rbp+16] ; rbx = env
mov rcx, 0 ;rcx = major
GET_N_ITEM rdx, rbx, rcx ; rdx = specific env
mov rbx, 0; rbx = minor
GET_N_ITEM rax, rdx, rbx
mov rax, qword [rax]
push rax
mov rax, rsp
mov rax, 0x3
push rax
mov rax, qword [fvar_tbl+8]
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]
push rax
mov rbx, qword [rbp+16] ; rbx = env
mov rcx, 0 ;rcx = major
GET_N_ITEM rdx, rbx, rcx ; rdx = specific env
mov rbx, 0; rbx = minor
GET_N_ITEM rax, rdx, rbx
pop qword [rax]
mov rax, SOB_VOID_ADDRESS
mov rbx, qword [rbp+16] ; rbx = env
mov rcx, 0 ;rcx = major
GET_N_ITEM rdx, rbx, rcx ; rdx = specific env
mov rbx, 0; rbx = minor
GET_N_ITEM rax, rdx, rbx
mov rax, qword [rax]
leave
ret
Lcont1:
push rax
push 3
mov rax, qword [fvar_tbl+112]
CLOSURE_ENV rbx, rax
push rbx
push qword [rbp+8]
push rax
FIX_STACK
pop rax
CLOSURE_CODE rbx, rax
jmp rbx
leave
ret
Lcont3:
leave
ret
Lcont4:
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]
mov qword [rbp+32], rax
mov rax, SOB_VOID_ADDRESS
push SOB_NIL_ADDRESS
mov rax, rsp
mov rax, 0x1
push rax
push SOB_NIL_ADDRESS
mov rax, qword [rbp+32]
push rax
mov rax, rsp
mov rax, 0x2
push rax
mov rax, qword [fvar_tbl+88]
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]
push SOB_NIL_ADDRESS
push 1
push SOB_NIL_ADDRESS
mov rax, qword [rbp+32]
push rax
mov rax, rsp
mov rax, 0x2
push rax
mov rax, qword [fvar_tbl+80]
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]
CLOSURE_ENV rbx, rax
push rbx
push qword [rbp+8]
push rax
FIX_STACK
pop rax
CLOSURE_CODE rbx, rax
jmp rbx
leave
ret
Lcont5:
CLOSURE_ENV rbx, rax
push rbx
CLOSURE_CODE rbx, rax
call rbx
add rsp, 8 ; pop env

    pop rbx ; pop arg count

    lea rsp , [rsp + 8*rbx]

	call write_sob_if_not_void;;; Clean up the dummy frame, set the exit status to 0 ("success"), 
   ;;; and return from main
   pop rbp
   add rsp, 3*8
   mov rax, 0

   ret
boolean?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_BOOL
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

flonum?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_FLOAT
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

rational?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_RATIONAL
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

pair?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_PAIR
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

null?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_NIL
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

char?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_CHAR
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

string?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_STRING
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

symbol?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_SYMBOL
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

procedure?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov sil, byte [rsi]
	cmp sil, T_CLOSURE
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

div:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne .div_rat
             FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  divsd xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)
             jmp .op_return
          .div_rat:
             DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          MAKE_RATIONAL(rax, rdx, rdi)
         mov PVAR(1), rax
         pop rbp
         jmp mul
	  mov rax, rcx
	  mov rdi, rsi
          .gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:
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
          MAKE_RATIONAL(rax, rsi, rcx)
          .op_return:
         pop rbp
         ret

mul:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne .mul_rat
             FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  mulsd xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)
             jmp .op_return
          .mul_rat:
             DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          imul rsi, rdi
	 imul rcx, rdx
	  mov rax, rcx
	  mov rdi, rsi
          .gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:
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
          MAKE_RATIONAL(rax, rsi, rcx)
          .op_return:
         pop rbp
         ret

add:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne .add_rat
             FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  addsd xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)
             jmp .op_return
          .add_rat:
             DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          imul rsi, rdx
	 imul rdi, rcx
	 add rsi, rdi
	 imul rcx, rdx
	  mov rax, rcx
	  mov rdi, rsi
          .gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:
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
          MAKE_RATIONAL(rax, rsi, rcx)
          .op_return:
         pop rbp
         ret

eq:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne .eq_rat
             FLOAT_VAL rsi, rsi
	 FLOAT_VAL rdi, rdi
	 cmp rsi, rdi
             jmp .op_return
          .eq_rat:
             NUMERATOR rcx, rsi
	 NUMERATOR rdx, rdi
	 cmp rcx, rdx
	 jne .false
	 DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 cmp rcx, rdx
         .false:
          .op_return:
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

lt:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne .lt_rat
             FLOAT_VAL rsi, rsi
	 movq xmm0, rsi
	 FLOAT_VAL rdi, rdi
	 movq xmm1, rdi
	 cmpltpd xmm0, xmm1
         movq rsi, xmm0
         cmp rsi, 0
             jmp .op_return
          .lt_rat:
             DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 NUMERATOR rsi, rsi
	 NUMERATOR rdi, rdi
	 imul rsi, rdx
	 imul rdi, rcx
	 cmp rsi, rdi
          .op_return:
      jl .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

string_length:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	STRING_LENGTH rsi, rsi
         MAKE_RATIONAL(rax, rsi, 1)
         pop rbp
         ret

string_ref:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         mov sil, byte [rsi]
         MAKE_CHAR(rax, sil)
         pop rbp
         ret

string_set:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	mov rdx, PVAR(2)
	STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         CHAR_VAL rax, rdx
         mov byte [rsi], al
         mov rax, SOB_VOID_ADDRESS
         pop rbp
         ret

make_string:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	NUMERATOR rsi, rsi
         CHAR_VAL rdi, rdi
         and rdi, 255
         MAKE_STRING rax, rsi, dil
         pop rbp
         ret

symbol_to_string:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	SYMBOL_VAL rsi, rsi
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
         .end:
         pop rbp
         ret

eq?:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	cmp rsi, rdi
      je .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:
         pop rbp
         ret

char_to_integer:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	CHAR_VAL rsi, rsi
	 and rsi, 255
	 MAKE_RATIONAL(rax, rsi, 1)
         pop rbp
         ret

integer_to_char:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	NUMERATOR rsi, rsi
	 and rsi, 255
	 MAKE_CHAR(rax, sil)
         pop rbp
         ret

exact_to_inexact:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	DENOMINATOR rdi, rsi
	 NUMERATOR rsi, rsi 
	 cvtsi2sd xmm0, rsi
	 cvtsi2sd xmm1, rdi
	 divsd xmm0, xmm1
	 movq rsi, xmm0
	 MAKE_FLOAT(rax, rsi)
         pop rbp
         ret

numerator:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	NUMERATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)
         pop rbp
         ret

denominator:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	DENOMINATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)
         pop rbp
         ret

gcd:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	xor rdx, rdx
	 NUMERATOR rax, rsi
         NUMERATOR rdi, rdi
         .gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:
	 mov rdx, rax
         cmp rdx, 0
         jge .make_result
         neg rdx
         .make_result:
         MAKE_RATIONAL(rax, rdx, 1)
         pop rbp
         ret

car:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rax, qword [rsi+TYPE_SIZE]
         pop rbp
         ret

cdr:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rax, qword [rsi+TYPE_SIZE+WORD_SIZE]
         pop rbp
         ret

cons:
       push rbp
       mov rbp, rsp 
       mov rsi, PVAR(0)
	mov rdi, PVAR(1)
	MAKE_PAIR(rax, rsi, rdi)
         pop rbp
         ret