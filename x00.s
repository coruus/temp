	.section	__TEXT,__text,regular,pure_instructions
	.macosx_version_min 10, 9
	.globl	_test
	.align	4, 0x90
_test:                                  ## @test
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp0:
	.cfi_def_cfa_offset 16
Ltmp1:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp2:
	.cfi_def_cfa_register %rbp
	andq	$-32, %rsp
	subq	$288, %rsp              ## imm = 0x120
	movq	%rdi, 264(%rsp)
	vmovaps	%ymm0, 224(%rsp)
	vmovaps	%ymm1, 192(%rsp)
	vmovaps	%ymm2, 160(%rsp)
	vmovaps	%ymm3, 128(%rsp)
	movq	%rsi, 120(%rsp)
	vmovaps	224(%rsp), %ymm0
	vmovaps	%xmm0, %xmm4
	vmovaps	192(%rsp), %ymm0
	vmovaps	%xmm0, %xmm5
	vpextrq	$1, %xmm5, %rsi
	vmovaps	160(%rsp), %ymm0
	vextracti128	$1, %ymm0, %xmm5
	vmovaps	128(%rsp), %ymm0
	vextracti128	$1, %ymm0, %xmm6
	vpextrq	$1, %xmm6, %rdi
	vmovq	%rdi, %xmm6
	vpunpcklqdq	%xmm6, %xmm5, %xmm5 ## xmm5 = xmm5[0],xmm6[0]
	vmovq	%rsi, %xmm6
	vpunpcklqdq	%xmm6, %xmm4, %xmm4 ## xmm4 = xmm4[0],xmm6[0]
                                        ## implicit-def: YMM0
	vmovaps	%xmm4, %xmm0
	vinserti128	$1, %xmm5, %ymm0, %ymm0
	vmovaps	%ymm0, 64(%rsp)
	movq	264(%rsp), %rsi
	vmovups	%ymm0, (%rsi)
	vmovaps	192(%rsp), %ymm0
	vmovaps	%xmm0, %xmm4
	vpextrq	$1, %xmm4, %rsi
	vmovaps	160(%rsp), %ymm0
	vextracti128	$1, %ymm0, %xmm4
	vmovaps	128(%rsp), %ymm0
	vextracti128	$1, %ymm0, %xmm5
	vpextrq	$1, %xmm5, %rdi
	vmovq	%rdi, %xmm5
	vmovq	120(%rsp), %xmm6
	vpunpcklqdq	%xmm6, %xmm5, %xmm5 ## xmm5 = xmm5[0],xmm6[0]
	vmovq	%rsi, %xmm6
	vpunpcklqdq	%xmm4, %xmm6, %xmm4 ## xmm4 = xmm6[0],xmm4[0]
                                        ## implicit-def: YMM0
	vmovaps	%xmm4, %xmm0
	vinserti128	$1, %xmm5, %ymm0, %ymm0
	vmovaps	%ymm0, 32(%rsp)
	movq	264(%rsp), %rsi
	vmovups	%ymm0, 32(%rsi)
	vmovaps	160(%rsp), %ymm0
	vextracti128	$1, %ymm0, %xmm4
	vmovaps	128(%rsp), %ymm0
	vextracti128	$1, %ymm0, %xmm5
	vpextrq	$1, %xmm5, %rsi
	vmovaps	224(%rsp), %ymm0
	vmovaps	%xmm0, %xmm5
	vmovq	120(%rsp), %xmm6
	vpunpcklqdq	%xmm5, %xmm6, %xmm5 ## xmm5 = xmm6[0],xmm5[0]
	vmovq	%rsi, %xmm6
	vpunpcklqdq	%xmm6, %xmm4, %xmm4 ## xmm4 = xmm4[0],xmm6[0]
                                        ## implicit-def: YMM0
	vmovaps	%xmm4, %xmm0
	vinserti128	$1, %xmm5, %ymm0, %ymm0
	vmovaps	%ymm0, (%rsp)
	movq	264(%rsp), %rsi
	vmovups	%ymm0, 64(%rsi)
	movq	%rbp, %rsp
	popq	%rbp
	vzeroupper
	retq
	.cfi_endproc


.subsections_via_symbols
