#include "./user_define.h"
.globl _start
.section .text
_start:
                  #include "./user_init.s"
                  csrr x5, 0xf14
                  add a0, zero, zero
                  add a1, zero, zero
                  li x6, 0
                  beq x5, x6, 0f

0: la x11, h0_start
jalr x0, x11, 0
h0_start:
kernel_sp:
                  la x15, kernel_stack_end

trap_vec_init:
                  la x31, mtvec_handler
                  ori x31, x31, 0
                  csrw 0x305, x31 # MTVEC

mepc_setup:
                  la x31, init
                  csrw 0x341, x31

custom_csr_setup:
                  nop

init_machine_mode:
                  li x31, 0xa00183a00
                  csrw 0x300, x31 # MSTATUS
                  li x31, 0x0
                  csrw 0x304, x31 # MIE
                  mret
init:
                  li x31, 2139095040
                  fmv.w.x f0, x31
                  li x31, 204554154
                  fmv.w.x f1, x31
                  li x31, 2152908622
                  fmv.w.x f2, x31
                  li x31, 4286578688
                  fmv.w.x f3, x31
                  li x31, 2144615610
                  fmv.w.x f4, x31
                  li x31, 2139095040
                  fmv.w.x f5, x31
                  li x31, 4286578688
                  fmv.w.x f6, x31
                  li x31, 4287275960
                  fmv.w.x f7, x31
                  li x31, 2771698
                  fmv.w.x f8, x31
                  li x31, 4292668182
                  fmv.w.x f9, x31
                  li x31, 4289231794
                  fmv.w.x f10, x31
                  li x31, 4286578688
                  fmv.w.x f11, x31
                  li x31, 4286578688
                  fmv.w.x f12, x31
                  li x31, 2872231273
                  fmv.w.x f13, x31
                  li x31, 2147483648
                  fmv.w.x f14, x31
                  li x31, 2139816533
                  fmv.w.x f15, x31
                  li x31, 2146286164
                  fmv.w.x f16, x31
                  li x31, 2139095039
                  fmv.w.x f17, x31
                  li x31, 4286578687
                  fmv.w.x f18, x31
                  li x31, 0
                  fmv.w.x f19, x31
                  li x31, 2139095040
                  fmv.w.x f20, x31
                  li x31, 4286578688
                  fmv.w.x f21, x31
                  li x31, 2139095039
                  fmv.w.x f22, x31
                  li x31, 4286578688
                  fmv.w.x f23, x31
                  li x31, 38116210
                  fmv.w.x f24, x31
                  li x31, 4286578687
                  fmv.w.x f25, x31
                  li x31, 4286578687
                  fmv.w.x f26, x31
                  li x31, 4286578688
                  fmv.w.x f27, x31
                  li x31, 7694094
                  fmv.w.x f28, x31
                  li x31, 587528732
                  fmv.w.x f29, x31
                  li x31, 0
                  fmv.w.x f30, x31
                  li x31, 4294615218
                  fmv.w.x f31, x31
                  fsrmi 1
                  li x0, 0x7
                  li x1, 0x820fa661
                  li x2, 0xff3ae6f2
                  li x3, 0xf9b1c46a
                  li x4, 0x9aa95d12
                  li x5, 0xfbe2dad0
                  li x6, 0x5a00ff83
                  li x7, 0xfda004f4
                  li x8, 0xc
                  li x9, 0xf2c2821d
                  li x10, 0xfa1d5e07
                  li x11, 0x2cf3ae79
                  li x12, 0xf7fbbd58
                  li x13, 0xf2a4462d
                  li x14, 0xf24d7f3b
                  li x17, 0x0
                  li x18, 0xb719417f
                  li x19, 0x76760321
                  li x20, 0xb1a800fd
                  li x21, 0xfeb3c52a
                  li x22, 0xf3b6e5ab
                  li x23, 0xfa872142
                  li x24, 0x6
                  li x25, 0x91c71928
                  li x26, 0xfdb288e4
                  li x27, 0xf5e2671f
                  li x28, 0x80000000
                  li x29, 0x2
                  li x30, 0xc0ac8c4d
                  li x31, 0xf11b100d
                  vsetvli x31, zero, e32, m1, ta, ma
                  la x31, region_2+1772
                  vle32.v v0, (x31)
                  la x31, region_0+3404
                  vle32.v v1, (x31)
                  la x31, region_0+1144
                  vle32.v v2, (x31)
                  la x31, region_0+956
                  vle32.v v3, (x31)
                  la x31, region_0+1992
                  vle32.v v4, (x31)
                  la x31, region_2+6152
                  vle32.v v5, (x31)
                  la x31, region_0+3528
                  vle32.v v6, (x31)
                  la x31, region_1+39732
                  vle32.v v7, (x31)
                  la x31, region_0+1672
                  vle32.v v8, (x31)
                  la x31, region_2+5368
                  vle32.v v9, (x31)
                  la x31, region_1+27396
                  vle32.v v10, (x31)
                  la x31, region_1+10172
                  vle32.v v11, (x31)
                  la x31, region_0+2688
                  vle32.v v12, (x31)
                  la x31, region_2+7132
                  vle32.v v13, (x31)
                  la x31, region_1+38176
                  vle32.v v14, (x31)
                  la x31, region_1+38996
                  vle32.v v15, (x31)
                  la x31, region_2+6852
                  vle32.v v16, (x31)
                  la x31, region_2+368
                  vle32.v v17, (x31)
                  la x31, region_0+732
                  vle32.v v18, (x31)
                  la x31, region_2+5624
                  vle32.v v19, (x31)
                  la x31, region_2+264
                  vle32.v v20, (x31)
                  la x31, region_1+33688
                  vle32.v v21, (x31)
                  la x31, region_1+3568
                  vle32.v v22, (x31)
                  la x31, region_1+55240
                  vle32.v v23, (x31)
                  la x31, region_2+5088
                  vle32.v v24, (x31)
                  la x31, region_1+57452
                  vle32.v v25, (x31)
                  la x31, region_2+128
                  vle32.v v26, (x31)
                  la x31, region_2+2756
                  vle32.v v27, (x31)
                  la x31, region_1+37592
                  vle32.v v28, (x31)
                  la x31, region_1+60188
                  vle32.v v29, (x31)
                  la x31, region_1+38892
                  vle32.v v30, (x31)
                  la x31, region_0+24
                  vle32.v v31, (x31)
                  csrwi vxsat, 1
                  csrwi vxrm, 3
                  li x9, 268
                  vsetvli x31, x9, e16, m4, ta, ma
                  la x16, user_stack_end
