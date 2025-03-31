.section .text.init # linker defines this section @ 0x8000
.global _start
_start:
_init:
  /* Initialize all gpr */
  li x1, 0
  li x2, 0
  li x3, 0
  li x4, 0
  li x5, 0
  li x6, 0
  li x7, 0
  li x8, 0
  li x9, 0
  li x10, 0
  li x11, 0
  li x12, 0
  li x13, 0
  li x14, 0
  li x15, 0
  li x16, 0
  li x17, 0
  li x18, 0
  li x19, 0
  li x20, 0
  li x21, 0
  li x22, 0
  li x23, 0
  li x24, 0
  li x25, 0
  li x26, 0
  li x27, 0
  li x28, 0
  li x29, 0
  li x30, 0
  li x31, 0
_code:
  addi x5, x6, 0x123 # test instr
  la x10, tohost # spike/sim end of test communication mechanism
  addi x11, x0, 0x1 # EXIT_CODE:0(success), END_SIM:1
  sw x11, 0(x10) # write tohost
  # write 1,2,3... to addr+4, +8, +12...
  addi x12, x10, 4 # next addr
  addi x13, x0, 0x1
  sw x13, 0(x12)
  addi x13, x13, 0x1
  sw x13, 4(x12)
  addi x13, x13, 0x1
  sw x13, 8(x12)
  addi x13, x13, 0x1
  sw x13, 12(x12)
  addi x13, x13, 0x1
  sw x13, 16(x12)
  fence.i
  # wait for end of sim to be polled
_loop_start:
  nop
  j _loop_start

.section .tohost
.global tohost
tohost: .dword 0
fromhost: .dword 0
