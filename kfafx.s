[CPU intelnop]
[bits 64]

[section .data]

align 32

__rho_00_03_l:
dq 0, 1, 62, 28
__rho_00_03_r:
dq 64, 64-1, 64-62, 64-28

__rho_05_08_l:
dq 36, 44, 6, 55
__rho_05_08_r:
dq 64-36, 64-44, 64-6, 64-55

__rho_10_13_l:
dq 3, 10, 43, 25
__rho_10_13_r:
dq 64-3,64-10,64-43,64-25

__rho_15_18_l:
dq 41,45,15,21
__rho_15_18_r:
dq 64-41,64-45,64-15,64-21

__rho_20_23_l:
dq 18,2,61,56
__rho_20_23_r:
dq 64-18,64-2,64-61,64-56


[section .text]

align 32
global _theta
_theta:
; scratch == RAX, RCX, RDX, RSI, RDI, R8-R11,
%define arg1 rdi
%define arg2 rsi
%define arg3 rdx
%define arg4 rcx
%define arg5 r8
%define arg6 r9

%define state(x) [arg1 + (x*8)]
%define A state
%define Cs(x)    [arg1 + 25*8 + (x*8)]
%define Ds(x)    [arg1 + 25*8 + 9*8 + (x*8)]
%define r0 rcx
%define r1 rdx
%define y0 ymm0
%define y1 ymm1
%define y2 ymm2
%define y3 ymm3
%define y4 ymm4
%define y5 ymm5
%define y6 ymm6
%define y7 ymm7
%define y8 ymm8
%define y9 ymm9
%define y10 ymm10

%define INTER 1

vzeroupper
rdtsc
shl rdx, 32
add rax, rdx
mov r8, rax

vmovdqu y0, state(0 ) ; y0 = { x[ 0], x[ 1], x[ 2], x[ 3] }
vmovdqu y1, state(5 ) ; y1 = { x[ 5], x[ 6], x[ 7], x[ 8] }
vmovdqu y2, state(10) ; y2 = { x[10], x[11], x[12], x[13] }
vmovdqu y3, state(15) ; y3 = { x[15], x[16], x[17], x[18] }
vmovdqu y4, state(20) ; y4 = { x[20], x[21], x[22], x[23] }

; copy up for use after parity
vmovdqa y5, y0
vmovdqa y6, y1
vmovdqa y7, y2
vmovdqa y8, y3
vmovdqa y9, y4

;; compute C[4]
mov r0, state(4 ) ; r0    =        x[ 4]
mov r1, state(9 ) ; r1    =        x[ 9]
xor r0, state(14) ; r0'   = r0   ^ x[14]
xor r1, state(19) ; r1'   = r1   ^ x[19]
xor r0, state(24) ; r0''  = r0'  ^ x[24]
xor r0, r1        ; r0''' = r0'' ^ r1'
;; r0 == C[4]
mov Ds(0), r0     ; Cs(4) = r0 = C[4]

;; compute C[0..3]
vpxor y0, y0, y1  ; y0'   = y0   ^ y1
vpxor y2, y2, y3  ; y2'   = y2   ^ y3
vpxor y0, y0, y4  ; y0''  = y0'  ^ y4  == y0 ^ y1 ^ y4
vpxor y0, y0, y2  ; y0''' = y0'' ^ y2' == y0 ^ y1 ^ y4 ^ y2 ^ y3
;; y0 == { C[0], C[1], C[2], C[3] }

;vmovdqu Ds(0), y0
vpbroadcastq y3, Ds(0)
;; y3 == { C[3], C[3], C[3], C[3] }
;vmovdqu Cs(0), y0
;; Cs[0..4] == C[0..4]
;vpermq y1, y0, 11111001b
;vpermq y0, y0, 10010000b
vpermq y1, y0, 11111001b
;; y1 == { C[1], C[2], C[3], ___ }
vpermq y0, y0, 10010000b
;; y0 == { ___,  C[0], C[1], C[2] }
vpblendd y1, y1, y3, 11000000b
;; y1 == { C[1], C[2], C[3], C[4] }
vpblendd y0, y0, y3, 00000011b 
;; y0 == { C[4], C[0], C[1], C[2] }

rorx    r0, Cs(0 ), 63 ; r1   = C[1] <<< 1
xor     r0, Cs(3 )     ; r1'  = r1 ^ C[4]  = D[0]
;  mov     Ds(4 ), r0
xor     A( 4), r0
xor     A( 9), r0
xor     A(14), r0
xor     A(19), r0
xor     A(24), r0

rorx r0, A(4), 64-27
mov A(4), r0
rorx r1, A(9), 64-20
mov A(9), r1
rorx r0, A(14), 64-39
mov A(14), r0
rorx r1, A(19), 64-8
mov A(19), r1
rorx r0, A(24), 64-14
mov A(24), r0

vpsllq y2, y1, 1
vpsrlq y1, y1, 63
;; y2 == y1 <<< 1

vpxor  y1, y1, y2
vpxor  y0, y0, y1

vpxor   y1, y0, y5  ;; y1 = A[0..3]
vpxor   y2, y0, y6  ;; y2 = A[5..8] 
vpxor   y3, y0, y7  ;; y3 = A[10..13]
vpxor   y4, y0, y8  ;; y4 = A[15..18]
vpxor   y5, y0, y9  ;; y5 = A[20..23]

vpsllvq  y6, y1, [rel __rho_00_03_l]
vpsrlvq  y1, y1, [rel __rho_00_03_r]

vpsllvq  y7, y2, [rel __rho_05_08_l]
vpsrlvq  y2, y2, [rel __rho_05_08_r]

vpsllvq  y8, y3, [rel __rho_10_13_l]  
vpsrlvq  y3, y3, [rel __rho_10_13_r] 

vpsllvq  y9, y4, [rel __rho_15_18_l]
vpsrlvq  y4, y4, [rel __rho_15_18_r]

vpsllvq  y10, y5, [rel __rho_20_23_l]
vpsrlvq  y5, y5,  [rel __rho_20_23_r]

vpxor    y1, y1, y6
vpxor    y2, y2, y7
vpxor    y3, y3, y8
vpxor    y4, y4, y9
vpxor    y5, y5, y10



  ;vmovdqu Ds(0), y0


  ;vmovdqu Cs(0 ), y0     ; Cs(0..3) = y0
  ;vmovdqu Cs(5 ), y1     ; Cs(5..8) = y0

%if INTER
  vmovdqu A(0), y1
  vmovdqu A(5), y2
  vmovdqu A(10), y3
  vmovdqu A(15), y4
  vmovdqu A(20), y5
%endif

rdtsc
shl rdx, 32
add rax, rdx
sub rax, r8

vzeroall
ret

; Cs = [ C[0], C[1], C[2], C[3], C[4] ]


; C[0], C[1], C[2], C[3]
; C[2], C[3], C[4], xxxx


; C[1], C[2], C[3], C[4]
; C[3], C[4], C[0], C[1]



; D = { C[4] ^ rol(
