.section .text.init # linker defines this section @ 0x8000
.global _start
_start:
_init: # random values
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
_code:
_ld_st_0: # data section @ 0x80002000
    li x26,  0x200000289a
    li x8, 0x2000002c78
    lb x25, 1092(x8)
    sllw x25, x21, x30
    and x15, x1, x27
    add x24, x11, x2
    subw x29, x21, x13
    lbu x10, 274(x26)
    lw x19, 1830(x26)
    srli x12, x19, 0x19
    sb x5, -1416(x26)
    srl x19, x1, x7
    sb x0, -1148(x26)
    sb x23, -54(x26)
    srlw x23, x21, x26
    sb x21, -35(x26)
    sllw x12, x7, x23
    lh x15, 1416(x8)
    srlw x22, x11, x28
    sra x20, x18, x1
    addi x12, x17, 0x1af
    srai x29, x2, 0xe
_ld_st_1:
    li x4, 0x2000002e0f
    li x19, 0x2000002514
    or x21, x11, x8
    sh x3, -498(x19)
    sh x29, 810(x19)
    srlw x16, x13, x23
    sb x10, -68(x19)
    lh x25, -128(x19)
    srl x30, x30, x3
    lbu x23, -305(x19)
    lbu x30, 1520(x4)
    sb x16, 1861(x19)
    andi x12, x10, 0x3cb
    sb x14, 1729(x4)
    lbu x29, -1629(x19)
    or x7, x27, x22
    lh x24, 1494(x19)
    lbu x11, -1889(x19)
    or x11, x4, x14
    srai x21, x26, 0x1e
    sltiu x22, x13, 0xb
    addi x8, x23, -0x51c
_ld_st_2:
    li x28, 0x2000002564
    li x17, 0x200000278a
    srlw x7, x21, x4
    andi x4, x30, 0x5c8
    addw x4, x6, x28
    lhu x20, -788(x17)
    lb x25, -1031(x28)
    andi x16, x2, -0xf8
    sub x12, x12, x24
    nop
    lbu x21, 1699(x17)
    slti x6, x9, -0x593
    slt x23, x2, x11
    xor x4, x23, x2
    or x3, x25, x27
    xor x3, x4, x17
    subw x8, x23, x9
    xori x9, x21, -0x329
    sh x14, -1034(x28)
    slli x30, x12, 0x1
    sra x21, x17, x29
    lhu x15, 1446(x28)
_spike_success:
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
