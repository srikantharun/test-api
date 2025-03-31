.section .text.init # linker defines this section @ 0x8000
.global _start
_start:
_init: # random values
    li x21, 0xa00082000 # Enable FPU
    csrw 0x300, x21 # MSTATUS
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
    li x21, 2147483648
    fmv.w.x f0, x21
    li x21, 4286578687
    fmv.w.x f1, x21
    li x21, 2139095040
    fmv.w.x f2, x21
    li x21, 3424002783
    fmv.w.x f3, x21
    li x21, 200740198
    fmv.w.x f4, x21
    li x21, 2150902476
    fmv.w.x f5, x21
    li x21, 5550792
    fmv.w.x f6, x21
    li x21, 2139095039
    fmv.w.x f7, x21
    li x21, 2143289344
    fmv.w.x f8, x21
    li x21, 2815482129
    fmv.w.x f9, x21
    li x21, 2143289344
    fmv.w.x f10, x21
    li x21, 4286578687
    fmv.w.x f11, x21
    li x21, 464806206
    fmv.w.x f12, x21
    li x21, 2139095041
    fmv.w.x f13, x21
    li x21, 2139095040
    fmv.w.x f14, x21
    li x21, 949437703
    fmv.w.x f15, x21
    li x21, 2139095041
    fmv.w.x f16, x21
    li x21, 2143289344
    fmv.w.x f17, x21
    li x21, 1145054093
    fmv.w.x f18, x21
    li x21, 2139095041
    fmv.w.x f19, x21
    li x21, 2147483648
    fmv.w.x f20, x21
    li x21, 2147483648
    fmv.w.x f21, x21
    li x21, 3371791
    fmv.w.x f22, x21
    li x21, 1114287439
    fmv.w.x f23, x21
    li x21, 2139095039
    fmv.w.x f24, x21
    li x21, 5995959
    fmv.w.x f25, x21
    li x21, 2143289344
    fmv.w.x f26, x21
    li x21, 4286578688
    fmv.w.x f27, x21
    li x21, 2139095041
    fmv.w.x f28, x21
    li x21, 4286578688
    fmv.w.x f29, x21
    li x21, 3099717745
    fmv.w.x f30, x21
    li x21, 2139095041
    fmv.w.x f31, x21
_code:
_fp_0:
    li x22,  0x2000002000 # data section start

    fsrmi 0 # RNE
    li x21, 0x3fc00000 # 1.5f
    fmv.w.x f31, x21
    fcvt.w.s x21, f31 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f31 # convert to unsigned int
    fsflagsi 0x00
    fsw f31, 0(x22) # same but go through mem
    flw f30, 0(x22)
    fcvt.w.s x21, f30 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f30 # convert to unsigned int
    fsflagsi 0x00

    li x21, 0x3fffffff # 1.99999f
    fmv.w.x f31, x21
    fcvt.w.s x21, f31 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f31 # convert to unsigned int
    fsflagsi 0x00
    fsw f31, 0(x22) # same but go through mem
    flw f30, 0(x22)
    fcvt.w.s x21, f30 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f30 # convert to unsigned int
    fsflagsi 0x00

    li x21, 0x3f000002 # 0.5000001f
    fmv.w.x f31, x21
    fcvt.w.s x21, f31 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f31 # convert to unsigned int
    fsflagsi 0x00

    fsrmi 1 # RTZ

    li x21, 0x3fc00000 # 1.5f
    fmv.w.x f31, x21
    fcvt.w.s x21, f31 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f31 # convert to unsigned int
    fsflagsi 0x00

    li x21, 0x3fffffff # 1.99999f
    fmv.w.x f31, x21
    fcvt.w.s x21, f31 # convert to signed int
    fsflagsi 0x00
    fcvt.w.s x21, f31 # convert to unsigned int
    fsflagsi 0x00

    li x21, 0x3f000002 # 0.5000001f
    fmv.w.x f31, x21
    fcvt.w.s x21, f31 # convert to signed int
    fsflagsi 0x00
    fcvt.wu.s x21, f31 # convert to unsigned int
    fsflagsi 0x00

_spike_success:
  la x10, tohost # spike/sim end of test communication mechanism
  addi x11, x0, 0x1 # EXIT_CODE:0(success), END_SIM:1
  sw x11, 0(x10) # write tohost
  fence.i
  # wait for end of sim to be polled
_loop_start:
  nop
  wfi

.section .tohost
.global tohost
tohost: .dword 0
fromhost: .dword 0
