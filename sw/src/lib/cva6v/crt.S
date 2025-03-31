/*
 * crt.S - entrypoint and C runtime (CRT) setup for CVA6V cores
 */

#include "encoding.h"
#include "stack.h"

#if __riscv_xlen == 64
# define LREG ld
# define SREG sd
# define REGBYTES 8
#else
#error "XLEN != 64"
#endif

.section ".text.init"
.global _start
_start:
  li  x1, 0
  li  x2, 0
  li  x3, 0
  li  x4, 0
  li  x5, 0
  li  x6, 0
  li  x7, 0
  li  x8, 0
  li  x9, 0
  li  x10,0
  li  x11,0
  li  x12,0
  li  x13,0
  li  x14,0
  li  x15,0
  li  x16,0
  li  x17,0
  li  x18,0
  li  x19,0
  li  x20,0
  li  x21,0
  li  x22,0
  li  x23,0
  li  x24,0
  li  x25,0
  li  x26,0
  li  x27,0
  li  x28,0
  li  x29,0
  li  x30,0
  li  x31,0

  # enable FPU, vector, and accelerator if present
  li t0, MSTATUS_FS | MSTATUS_XS | MSTATUS_VS
  csrs mstatus, t0

#ifdef __riscv_flen
  # initialize FPU if we have one
  la t0, 1f
  csrw mtvec, t0

  fssr    x0
  fmv.s.x f0, x0
  fmv.s.x f1, x0
  fmv.s.x f2, x0
  fmv.s.x f3, x0
  fmv.s.x f4, x0
  fmv.s.x f5, x0
  fmv.s.x f6, x0
  fmv.s.x f7, x0
  fmv.s.x f8, x0
  fmv.s.x f9, x0
  fmv.s.x f10,x0
  fmv.s.x f11,x0
  fmv.s.x f12,x0
  fmv.s.x f13,x0
  fmv.s.x f14,x0
  fmv.s.x f15,x0
  fmv.s.x f16,x0
  fmv.s.x f17,x0
  fmv.s.x f18,x0
  fmv.s.x f19,x0
  fmv.s.x f20,x0
  fmv.s.x f21,x0
  fmv.s.x f22,x0
  fmv.s.x f23,x0
  fmv.s.x f24,x0
  fmv.s.x f25,x0
  fmv.s.x f26,x0
  fmv.s.x f27,x0
  fmv.s.x f28,x0
  fmv.s.x f29,x0
  fmv.s.x f30,x0
  fmv.s.x f31,x0
1:
#endif

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

  # initialize trap vector
  la t0, trap_entry
  csrw mtvec, t0

  # initialize global pointer
.option push
.option norelax
  la gp, __global_pointer$
.option pop

  # determine stack attributes:
  # - t0: relative hart ID (to first HART in processor)
  # - t1: stack shift = log2(stack size)
#ifndef SYSTEM_TOP
  # single core (assume id = 0)
  li t0, 1
  li t1, CVA6V_STANDALONE_STACK_SHIFT
#else
  ## read mhartid
  csrr t0, mhartid
  ## if (mhartid < 6): infinite loop (APU, should not happen)
  li t1, 6
  blt t0, t1, loop
  ## else if (mhartid < 14): aicores
  li t1, 14
  blt t0, t1, stack_attrs_aicores
  ## else if (mhartid < 22): pve0
  li t1, 22
  blt t0, t1, stack_attrs_pve0
  ## else if (mhartid < 30): pve1
  li t1, 30
  blt t0, t1, stack_attrs_pve1
  ## else: infinite loop (should not happen)
  j loop

stack_attrs_aicores:
  li t0, 0 # relative hart ID = 0
  li t1, AICORE_STACK_SHIFT
  j stack_attrs_out
stack_attrs_pve0:
  addi t0, t0, -14
  li t1, PVE_STACK_SHIFT
  j stack_attrs_out
stack_attrs_pve1:
  addi t0, t0, -22
  li t1, PVE_STACK_SHIFT
  # no jump
stack_attrs_out:

#endif

  # initialize stack pointer (add 1 to get end of stack region)
  # stack_pointer = _stack_begin + ((relative_hart_id + 1) << stack_shift)
  la sp, _stack_begin
  addi t0, t0, 1
  sll t0, t0, t1
  add sp, sp, t0

  j _init


loop:
  wfi
  j loop

  .align 2
trap_entry:
  addi sp, sp, -288

  SREG x1, 1*REGBYTES(sp)
  SREG x2, 2*REGBYTES(sp)
  SREG x3, 3*REGBYTES(sp)
  SREG x4, 4*REGBYTES(sp)
  SREG x5, 5*REGBYTES(sp)
  SREG x6, 6*REGBYTES(sp)
  SREG x7, 7*REGBYTES(sp)
  SREG x8, 8*REGBYTES(sp)
  SREG x9, 9*REGBYTES(sp)
  SREG x10, 10*REGBYTES(sp)
  SREG x11, 11*REGBYTES(sp)
  SREG x12, 12*REGBYTES(sp)
  SREG x13, 13*REGBYTES(sp)
  SREG x14, 14*REGBYTES(sp)
  SREG x15, 15*REGBYTES(sp)
  SREG x16, 16*REGBYTES(sp)
  SREG x17, 17*REGBYTES(sp)
  SREG x18, 18*REGBYTES(sp)
  SREG x19, 19*REGBYTES(sp)
  SREG x20, 20*REGBYTES(sp)
  SREG x21, 21*REGBYTES(sp)
  SREG x22, 22*REGBYTES(sp)
  SREG x23, 23*REGBYTES(sp)
  SREG x24, 24*REGBYTES(sp)
  SREG x25, 25*REGBYTES(sp)
  SREG x26, 26*REGBYTES(sp)
  SREG x27, 27*REGBYTES(sp)
  SREG x28, 28*REGBYTES(sp)
  SREG x29, 29*REGBYTES(sp)
  SREG x30, 30*REGBYTES(sp)
  SREG x31, 31*REGBYTES(sp)

  # save mcause, mepc, mstatus
  csrr t0, mcause
  SREG t0, 32*REGBYTES(sp)
  csrr t0, mepc
  SREG t0, 33*REGBYTES(sp)
  csrr t0, mstatus
  SREG t0, 34*REGBYTES(sp)
  csrr t0, mtval
  SREG t0, 35*REGBYTES(sp)

  mv a0, sp
  jal trap_handler

  /* Disable interrupt */
  csrrci a5, mstatus, MSTATUS_MIE

  /* Restore mstatus and mepc */
  LREG t0, 33*REGBYTES(sp)  # Restore mepc
  LREG t1, 34*REGBYTES(sp)  # Restore mstatus

  csrw mepc, t0
  csrw mstatus, t1

  # Remain in M-mode after eret
  li t0, MSTATUS_MPP
  csrs mstatus, t0

  LREG x1, 1*REGBYTES(sp)
  LREG x2, 2*REGBYTES(sp)
  LREG x3, 3*REGBYTES(sp)
  LREG x4, 4*REGBYTES(sp)
  LREG x5, 5*REGBYTES(sp)
  LREG x6, 6*REGBYTES(sp)
  LREG x7, 7*REGBYTES(sp)
  LREG x8, 8*REGBYTES(sp)
  LREG x9, 9*REGBYTES(sp)
  LREG x10, 10*REGBYTES(sp)
  LREG x11, 11*REGBYTES(sp)
  LREG x12, 12*REGBYTES(sp)
  LREG x13, 13*REGBYTES(sp)
  LREG x14, 14*REGBYTES(sp)
  LREG x15, 15*REGBYTES(sp)
  LREG x16, 16*REGBYTES(sp)
  LREG x17, 17*REGBYTES(sp)
  LREG x18, 18*REGBYTES(sp)
  LREG x19, 19*REGBYTES(sp)
  LREG x20, 20*REGBYTES(sp)
  LREG x21, 21*REGBYTES(sp)
  LREG x22, 22*REGBYTES(sp)
  LREG x23, 23*REGBYTES(sp)
  LREG x24, 24*REGBYTES(sp)
  LREG x25, 25*REGBYTES(sp)
  LREG x26, 26*REGBYTES(sp)
  LREG x27, 27*REGBYTES(sp)
  LREG x28, 28*REGBYTES(sp)
  LREG x29, 29*REGBYTES(sp)
  LREG x30, 30*REGBYTES(sp)
  LREG x31, 31*REGBYTES(sp)

  addi sp, sp, 288
  mret

.weak trap_handler
trap_handler:
  wfi
  j trap_handler

/* Only define .tohost section if we are compliing standalone (i.e., without the APU). */
/* Otherwise, the section will be defined by the APU's crt.S. */
#ifndef SYSTEM_TOP
.section ".tohost","aw",@progbits
.align 6
.globl tohost
tohost: .dword 0
.align 6
.globl fromhost
fromhost: .dword 0
#endif
