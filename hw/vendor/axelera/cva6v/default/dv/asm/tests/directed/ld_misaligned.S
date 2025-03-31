#include "../../env/encoding.h"

.section .text.init # linker defines this section @ 0x8000
.global _start
_start:
_init:
trap_vec_init:
  la t6, mmode_trap_handler
  ori t6, t6, 0
  csrw CSR_MTVEC, t6 # MTVEC
regs_init:
  li x1, 0xaac85d
  li x2, 0x5adc871
  li x3, -0x771d0fda
  li x4, -0xef703aa
  li x5, 0x121e3560
  li x6, -0x59284e5e
  li x7, 0x1515c5cc
  li x8, -0x2578a8b2
  li x9, 0x16047848
  li x10, -0x369c727
  li x11, 0x5a38253b
  li x12, -0x5d787f5e
  li x13, -0x21757567
  li x14, -0xe462e85
  li x15, -0x6e5da8a4
  li x16, 0x7bc5706b
  li x17, 0x72a01ac3
  li x18, 0x346a1375
  li x19, -0x53be942
  li x20, -0x6c580f47
  li x21, -0x70dee16a
  li x22, -0x5a36d71e
  li x23, 0x45c7e3d0
  li x24, -0x5dd9728b
  li x25, 0x38c02ee6
  li x26, -0xad22a9b
  li x27, -0x61782410
  li x28, 0x5d6e756b
  li x29, 0x68a80ac7
  li x30, -0x3a565e42
  li x31, 0x75ad17d

code:
ld_st_0:
  li s10, 0x2000002800 # should be middle of data section
  lw zero, 8(s10) # aligned word
  lhu a0, 3(s10) # misaligned half-word
  lw s3, 1832(s10) # aligned
  lw s3, 1830(s10) # misaligned again
spike_success:
  la x10, tohost # spike/sim end of test communication mechanism
  addi x11, x0, 0x1 # EXIT_CODE:0(success), END_SIM:1
  sw x11, 0(x10) # write tohost
  fence.i
end_of_test_loop: # wait to be polled by spike
  nop
  j end_of_test_loop

.align 12
mmode_trap_handler:
  csrr t6, CSR_MCAUSE
  #srli x28, x29, 63 # get msb
  #bne x28, x0, mmode_intr_handler
  li t5, 0x4 # Misaligned Load Cause Value
  beq t6, t5, mmode_misaligned_load_handler
  mret # repeat the instruction for other causes

mmode_misaligned_load_handler:
  csrr	t5, CSR_MEPC
	addi	t5, t5, 4 # skip the troublesome instruction
	csrw	CSR_MEPC, t5
  csrw  CSR_MCAUSE, zero
	mret

.section .tohost
.global tohost
tohost: .dword 0
fromhost: .dword 0
