
%define C0 rax
%define C1 rbx
%define C2 rcx
%define C3 rdx
%define C4 rsi

%define D0 r10
%define D1 r11
%define D2 r12
%define D3 r13
%define D4 r14

%define t0 D0
%define t1 D1
%define t2 D2
%define t3 D3
%define t4 D4

%define A(i) [rdi+(i*8)]
%define D(i) [rdi+25*8+(i*8)]

%define rolq rol qword


section .text
align 32
global _kck
_kck:

.prelude:
push r10
push r11
push r12
push r13
push r14

.load:
mov C0, A(0)
mov C1, A(1)
mov C2, A(2)
mov C3, A(3)
mov C4, A(4)

;Ltheta:

xor C0, A(5)
xor C1, A(6)
xor C2, A(7)
xor C3, A(8)
xor C4, A(9)

;add Ai, 5*8
;dec r15
;jnz Ltheta

xor C0, A(10)
xor C1, A(11)
xor C2, A(12)
xor C3, A(13)
xor C4, A(14)

xor C0, A(15)
xor C1, A(16)
xor C2, A(17)
xor C3, A(18)
xor C4, A(19)

xor C0, A(20)
xor C1, A(21)
xor C2, A(22)
xor C3, A(23)
xor C4, A(24)

mov D0, C1
rol D0, 1
xor D0, C4

mov D1, C2
rol D1, 1
xor D1, C0

mov D2, C3
rol D2, 1
xor D2, C1

mov D3, C4
rol D3, 1
xor D3, C2

mov D4, C0
rol D4, 1
xor D4, C3

;; todo get rid of
mov C0, D0
mov C1, D1
mov C2, D2
mov C3, D3
mov C4, D4

xor A(0), C0
xor A(1), C1
xor A(2), C2
xor A(3), C3
xor A(4), C4

xor A(5), C0
xor A(6), C1
xor A(7), C2
xor A(8), C3
xor A(9), C4

xor A(10), C0
xor A(11), C1
xor A(12), C2
xor A(13), C3
xor A(14), C4

rolq A(1), 1 
rolq A(2), 62
rolq A(3), 28
rolq A(4), 27

rolq A(5), 36
rolq A(6), 44
rolq A(7), 6
rolq A(8), 55
rolq A(9), 20

rolq A(10), 3
rolq A(11), 10
rolq A(12), 43
rolq A(13), 25
rolq A(14), 39

xor A(15), C0
xor A(16), C1
xor A(17), C2
xor A(18), C3
xor A(19), C4

xor A(20), C0
xor A(21), C1
xor A(22), C2
xor A(23), C3
xor A(24), C4

rolq A(15), 41
rolq A(16), 45
rolq A(17), 15
rolq A(18), 21
rolq A(19), 8

rolq A(20), 18
rolq A(21), 2
rolq A(22), 61
rolq A(23), 56
rolq A(24), 14



.prologue:
pop r14
pop r13
pop r12
pop r11
pop r10

ret
