[CPU intelnop]
[bits 64]

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

vzeroall
rdtsc
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
mov Cs(4), r0     ; Cs(4) = r0 = C[4]

;; compute C[0..3]
vpxor y0, y0, y1  ; y0'   = y0   ^ y1
vpxor y2, y2, y3  ; y2'   = y2   ^ y3
vpxor y0, y0, y4  ; y0''  = y0'  ^ y4  == y0 ^ y1 ^ y4
vpxor y0, y0, y2  ; y0''' = y0'' ^ y2' == y0 ^ y1 ^ y4 ^ y2 ^ y3
;; y0 == { C[0], C[1], C[2], C[3] }

vmovdqu Cs(0 ), y0     ; Cs(0..3) = y0
vmovdqu Cs(5 ), y0     ; Cs(5..8) = y0
;; Cs = { C[0], C[1], C[2], C[3], C[4], C[0], C[1], C[2], C[3] }

;; { C[4], C[0], C[1], C[2] ]
;; { C[1], C[2], C[3], C[4] } <<< 1
;; { D[0], D[1], D[2], D[3] }
vmovdqu  y1, Cs(1)
vmovdqu  y0, Cs(4)

vpsllq  y2, y1, 1      ; y2   = y1 << 1
vpsrlq  y1, y1, 63     ; y1'  = y1 >> 63
vpxor   y1, y1, y2     ; y1'' = y1 ^ y2    =
vpxor   y0, y0, y1     ; y0'  = y0 ^ y1    = { D[1], D[2], D[3], D[4] }
vmovdqu Ds(0 ), y0

rorx    r0, Cs(0 ), 63 ; r1   = C[1] <<< 1
xor     r0, Cs(3 )     ; r1'  = r1 ^ C[4]  = D[0]
mov     Ds(4 ), r0

vpxor   y1, y0, y5
vpxor   y2, y0, y6  
vpxor   y3, y0, y7
vpxor   y4, y0, y8 
vpxor   y5, y0, y9

xor     A(9),  r0
xor     A(14), r0
xor     A(19), r0
xor     A(24), r0



rdtsc
sub rax, r8

vzeroall
ret

; Cs = [ C[0], C[1], C[2], C[3], C[4] ]


; C[0], C[1], C[2], C[3]
; C[2], C[3], C[4], xxxx


; C[1], C[2], C[3], C[4]
; C[3], C[4], C[0], C[1]



; D = { C[4] ^ rol(
