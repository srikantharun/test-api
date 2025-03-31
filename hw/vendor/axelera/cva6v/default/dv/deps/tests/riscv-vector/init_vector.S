#include "../../../asm/env/riscv_test.h"

#undef RVTEST_RV64S
#define RVTEST_RV64S RVTEST_RV64M

.global main

RVTEST_RV64S
RVTEST_CODE_BEGIN

  #define sscratch mscratch
  #define sstatus mstatus
  #define scause mcause
  #define sepc mepc
  #define sret mret
  #define stvec_handler mtvec_handler
  #undef SSTATUS_SPP
  #define SSTATUS_SPP MSTATUS_MPP

  #.align 4

  _set_machine_mode:
    li t0, MSTATUS_MPP
    csrc mstatus, t0
    csrr t1, mstatus
    and t0, t0, t1
    bnez t0, _init_fregs

  _init_fregs:
    /* Initialize floating point register */
    /* Set mstatus.FS */
    li x14, 0x1 << 13
    csrs mstatus, x14

    fmv.w.x f0, x0
    fmv.w.x f1, x0
    fmv.w.x f2, x0
    fmv.w.x f3, x0
    fmv.w.x f4, x0
    fmv.w.x f5, x0
    fmv.w.x f6, x0
    fmv.w.x f7, x0
    fmv.w.x f8, x0
    fmv.w.x f9, x0
    fmv.w.x f10, x0
    fmv.w.x f11, x0
    fmv.w.x f12, x0
    fmv.w.x f13, x0
    fmv.w.x f14, x0
    fmv.w.x f15, x0
    fmv.w.x f16, x0
    fmv.w.x f17, x0
    fmv.w.x f18, x0
    fmv.w.x f19, x0
    fmv.w.x f20, x0
    fmv.w.x f21, x0
    fmv.w.x f22, x0
    fmv.w.x f23, x0
    fmv.w.x f24, x0
    fmv.w.x f25, x0
    fmv.w.x f26, x0
    fmv.w.x f27, x0
    fmv.w.x f28, x0
    fmv.w.x f29, x0
    fmv.w.x f30, x0
    fmv.w.x f31, x0

  _init_vregs:

    /* Initialize vector register */

    /* Set mstatus.VS */
    li x14, 0x1 << 9
    csrs mstatus, x14

    vsetvli a1, zero, e32, m1, tu, mu
    vmv.v.i	v0, 0
    vmv.v.i	v1, 0
    vmv.v.i	v2, 0
    vmv.v.i	v3, 0
    vmv.v.i	v4, 0
    vmv.v.i	v5, 0
    vmv.v.i	v6, 0
    vmv.v.i	v7, 0
    vmv.v.i	v8, 0
    vmv.v.i	v9, 0
    vmv.v.i	v10, 0
    vmv.v.i	v11, 0
    vmv.v.i	v12, 0
    vmv.v.i	v13, 0
    vmv.v.i	v14, 0
    vmv.v.i	v15, 0
    vmv.v.i	v16, 0
    vmv.v.i	v17, 0
    vmv.v.i	v18, 0
    vmv.v.i	v19, 0
    vmv.v.i	v20, 0
    vmv.v.i	v21, 0
    vmv.v.i	v22, 0
    vmv.v.i	v23, 0
    vmv.v.i	v24, 0
    vmv.v.i	v25, 0
    vmv.v.i	v26, 0
    vmv.v.i	v27, 0
    vmv.v.i	v28, 0
    vmv.v.i	v29, 0
    vmv.v.i	v30, 0
    vmv.v.i	v31, 0

  _test_seq:

    li sp, 0x2800000000    # Load the end address of the DRAM into sp
    addi sp, sp, -16     # Adjust sp to reserve some space for the stack (16 bytes)
    // Jump to main
    jal main

    li TESTNUM, 0x1 # auto pass _test_seq

  TEST_PASSFAIL # checks _test_seq and main
RVTEST_CODE_END

.section .tohost
.global tohost
tohost:   .dword 0
fromhost: .dword 0

.section .data
vec1: .space 4096
vec2: .space 4096
vec3: .space 4096
vec4: .space 4096


