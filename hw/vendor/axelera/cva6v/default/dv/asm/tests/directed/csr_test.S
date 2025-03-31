.section .text.init # linker defines this section @ 0x8000
.global _start
_start:
_init:
  /* Initialize all gpr */
  li x21, 0xa00082200 # Enable FPU & VPU to inital
  csrw 0x300, x21 # MSTATUS
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
  # glab point 5 - mtvec
  csrr x20, mtvec
  li x21, 0xFFFFFFFF
  csrw  mtvec, x21
  csrr x20, mtvec
  li x21, 1
  csrw  mtvec, x21
  csrr x20, mtvec
  li x21, 0xFFFF1
  csrw  mtvec, x21
  csrr x20, mtvec
  # glab point 5 - stvec
  csrr x20, stvec
  li x21, 0xFFFFFFFF
  csrw  stvec, x21
  csrr x20, stvec
  li x21, 1
  csrw  stvec, x21
  csrr x20, stvec
  li x21, 0xFFFF1
  csrw  stvec, x21
  csrr x20, stvec
  # glab #549 point 1 - misa D ext set
  csrr x20, misa
  li x21, 0xFFFFFFFF
  csrw  misa, x21
  csrr x20, misa
  # glab #1701 point 2 - vendor / arch
  csrr x20, mvendorid
  csrr x21, marchid
  # glab #1701 point 6 - fiom bit
  csrr x20, menvcfg
  addi x21, x0, 0x1
  csrs menvcfg, x21
  csrr x20, menvcfg
  csrrci  s4, menvcfg, 22
  li x21, 0xFF
  csrw menvcfg, x21
  csrr x20, menvcfg
  # S mode
  csrr x20, senvcfg
  addi x21, x0, 0x1
  csrs senvcfg, x21
  csrr x20, senvcfg
  csrrci  s4, senvcfg, 22
  li x21, 0xFF
  csrw senvcfg, x21
  csrr x20, senvcfg
  # glab #1701 point 8 - dirty state on V CSR read
  #csrr x20, vstart
  csrr x21, mstatus
  #csrr x20, vxsat
  csrr x21, mstatus
  #csrr x20, vxrm
  csrr x21, mstatus
  #csrr x20, vcsr
  csrr x21, mstatus
  #csrr x20, vl
  csrr x21, mstatus
  #csrr x20, vtype
  csrr x21, mstatus
  #csrr x20, vlenb
  csrr x21, mstatus
  la x10, tohost # spike/sim end of test communication mechanism
  addi x11, x0, 0x1 # EXIT_CODE:0(success), END_SIM:1
  sw x11, 0(x10) # write tohost
  fence.i
  # wait for end of sim to be polled
_loop_start:
  nop
  j _loop_start

.section .tohost
.global tohost
tohost: .dword 0
fromhost: .dword 0
