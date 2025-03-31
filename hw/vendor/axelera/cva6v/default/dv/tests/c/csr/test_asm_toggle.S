// full_arithmetic_sequence.S
// Loads all registers and then executes a series of arithmetic instructions
// Including scalar integer, floating-point, and vector operations
// Author: [Your Name]

    .section .text
    .globl run_toggle_bit_assembly_tests

run_toggle_bit_assembly_tests:
    # ---------------------------
    # Load Integer Registers with Values
    # ---------------------------

    # Load registers x1 to x31 with values
    # x0 is hardwired to zero and cannot be modified
    li x1, 1
    li x2, 2
    li x3, 3
    li x4, 4
    li x5, 5
    li x6, 6
    li x7, 7
    li x8, 8
    li x9, 9
    li x10, 10
    li x11, 11
    li x12, 12
    li x13, 13
    li x14, 14
    li x15, 15
    li x16, 16
    li x17, 17
    li x18, 18
    li x19, 19
    li x20, 20
    li x21, 21
    li x22, 22
    li x23, 23
    li x24, 24
    li x25, 25
    li x26, 26
    li x27, 27
    li x28, 28
    li x29, 29
    li x30, 30
    li x31, 31

 # ---------------------------

    #  'add' instructions
    add x1, x1, x2
    add x2, x3, x4
    add x3, x5, x6
    add x4, x7, x8
    add x5, x9, x10
    add x6, x11, x12
    add x7, x13, x14
    add x8, x15, x16
    add x9, x17, x18
    add x10, x19, x20
    add x11, x21, x22
    add x12, x23, x24
    add x13, x25, x26
    add x14, x27, x28
    add x15, x29, x30
    add x16, x31, x1
    add x17, x2, x3
    add x18, x4, x5
    add x19, x6, x7
    add x20, x8, x9
    add x21, x10, x11
    add x22, x12, x13
    add x23, x14, x15
    add x24, x16, x17
    add x25, x18, x19
    add x26, x20, x21
    add x27, x22, x23
    add x28, x24, x25
    add x29, x26, x27
    add x30, x28, x29
    add x31, x30, x1
    add x1, x2, x3
    add x2, x4, x5
    add x3, x6, x7
    add x4, x8, x9
    add x5, x10, x11
    add x6, x12, x13
    add x7, x14, x15
    add x8, x16, x17
    add x9, x18, x19
    add x10, x20, x21
    add x11, x22, x23
    add x12, x24, x25
    add x13, x26, x27
    add x14, x28, x29
    add x15, x30, x31
    add x16, x1, x2
    add x17, x3, x4
    add x18, x5, x6
    add x19, x7, x8
    add x20, x9, x10
    add x21, x11, x12
    add x22, x13, x14
    add x23, x15, x16
    add x24, x17, x18
    add x25, x19, x20
    add x26, x21, x22
    add x27, x23, x24
    add x28, x25, x26
    add x29, x27, x28
    add x30, x29, x30
    add x31, x31, x1

    # ---------------------------
    # Series of Add Immediate Instructions
    # ---------------------------

    #  'addi' instructions
    addi x1, x1, 1
    addi x2, x2, 2
    addi x3, x3, 3
    addi x4, x4, 4
    addi x5, x5, 5
    addi x6, x6, 6
    addi x7, x7, 7
    addi x8, x8, 8
    addi x9, x9, 9
    addi x10, x10, 10
    addi x11, x11, 11
    addi x12, x12, 12
    addi x13, x13, 13
    addi x14, x14, 14
    addi x15, x15, 15
    addi x16, x16, 16
    addi x17, x17, 17
    addi x18, x18, 18
    addi x19, x19, 19
    addi x20, x20, 20
    addi x21, x21, 21
    addi x22, x22, 22
    addi x23, x23, 23
    addi x24, x24, 24
    addi x25, x25, 25
    addi x26, x26, 26
    addi x27, x27, 27
    addi x28, x28, 28
    addi x29, x29, 29
    addi x30, x30, 30
    addi x31, x31, 31
    addi x1, x1, -1
    addi x2, x2, -2
    addi x3, x3, -3
    addi x4, x4, -4
    addi x5, x5, -5
    addi x6, x6, -6
    addi x7, x7, -7
    addi x8, x8, -8
    addi x9, x9, -9
    addi x10, x10, -10
    addi x11, x11, -11
    addi x12, x12, -12
    addi x13, x13, -13
    addi x14, x14, -14
    addi x15, x15, -15
    addi x16, x16, -16
    addi x17, x17, -17
    addi x18, x18, -18
    addi x19, x19, -19
    addi x20, x20, -20
    addi x21, x21, -21
    addi x22, x22, -22
    addi x23, x23, -23
    addi x24, x24, -24
    addi x25, x25, -25
    addi x26, x26, -26
    addi x27, x27, -27
    addi x28, x28, -28
    addi x29, x29, -29
    addi x30, x30, -30
    addi x31, x31, -31

    # ---------------------------
    # Series of Subtract Instructions
    # ---------------------------

    #  'sub' instructions
    sub x1, x1, x2
    sub x2, x3, x4
    sub x3, x5, x6
    sub x4, x7, x8
    sub x5, x9, x10
    sub x6, x11, x12
    sub x7, x13, x14
    sub x8, x15, x16
    sub x9, x17, x18
    sub x10, x19, x20
    sub x11, x21, x22
    sub x12, x23, x24
    sub x13, x25, x26
    sub x14, x27, x28
    sub x15, x29, x30
    sub x16, x31, x1
    sub x17, x2, x3
    sub x18, x4, x5
    sub x19, x6, x7
    sub x20, x8, x9
    sub x21, x10, x11
    sub x22, x12, x13
    sub x23, x14, x15
    sub x24, x16, x17
    sub x25, x18, x19
    sub x26, x20, x21
    sub x27, x22, x23
    sub x28, x24, x25
    sub x29, x26, x27
    sub x30, x28, x29
    sub x31, x30, x1
    sub x1, x2, x3
    sub x2, x4, x5
    sub x3, x6, x7
    sub x4, x8, x9
    sub x5, x10, x11
    sub x6, x12, x13
    sub x7, x14, x15
    sub x8, x16, x17
    sub x9, x18, x19
    sub x10, x20, x21
    sub x11, x22, x23
    sub x12, x24, x25
    sub x13, x26, x27
    sub x14, x28, x29
    sub x15, x30, x31
    sub x16, x1, x2
    sub x17, x3, x4
    sub x18, x5, x6
    sub x19, x7, x8
    sub x20, x9, x10
    sub x21, x11, x12
    sub x22, x13, x14
    sub x23, x15, x16
    sub x24, x17, x18
    sub x25, x19, x20
    sub x26, x21, x22
    sub x27, x23, x24
    sub x28, x25, x26
    sub x29, x27, x28
    sub x30, x29, x30
    sub x31, x31, x1

    # ---------------------------
    # Series of Multiply Instructions
    # ---------------------------

    #  'mul' instructions (assuming M extension)
    mul x1, x1, x2
    mul x2, x3, x4
    mul x3, x5, x6
    mul x4, x7, x8
    mul x5, x9, x10
    mul x6, x11, x12
    mul x7, x13, x14
    mul x8, x15, x16
    mul x9, x17, x18
    mul x10, x19, x20
    mul x11, x21, x22
    mul x12, x23, x24
    mul x13, x25, x26
    mul x14, x27, x28
    mul x15, x29, x30
    mul x16, x31, x1
    mul x17, x2, x3
    mul x18, x4, x5
    mul x19, x6, x7
    mul x20, x8, x9
    mul x21, x10, x11
    mul x22, x12, x13
    mul x23, x14, x15
    mul x24, x16, x17
    mul x25, x18, x19
    mul x26, x20, x21
    mul x27, x22, x23
    mul x28, x24, x25
    mul x29, x26, x27
    mul x30, x28, x29
    mul x31, x30, x1
    mul x1, x2, x3
    mul x2, x4, x5
    mul x3, x6, x7
    mul x4, x8, x9
    mul x5, x10, x11
    mul x6, x12, x13
    mul x7, x14, x15
    mul x8, x16, x17
    mul x9, x18, x19
    mul x10, x20, x21
    mul x11, x22, x23
    mul x12, x24, x25
    mul x13, x26, x27
    mul x14, x28, x29
    mul x15, x30, x31
    mul x16, x1, x2
    mul x17, x3, x4
    mul x18, x5, x6
    mul x19, x7, x8
    mul x20, x9, x10
    mul x21, x11, x12
    mul x22, x13, x14
    mul x23, x15, x16
    mul x24, x17, x18
    mul x25, x19, x20
    mul x26, x21, x22
    mul x27, x23, x24
    mul x28, x25, x26
    mul x29, x27, x28
    mul x30, x29, x30
    mul x31, x31, x1

    # ---------------------------
    # Series of Divide Instructions
    # ---------------------------

    #  'div' instructions (assuming M extension)
    # To avoid division by zero, ensure denominators are non-zero
    div x1, x1, x2
    div x2, x3, x4
    div x3, x5, x6
    div x4, x7, x8
    div x5, x9, x10
    div x6, x11, x12
    div x7, x13, x14
    div x8, x15, x16
    div x9, x17, x18
    div x10, x19, x20
    div x11, x21, x22
    div x12, x23, x24
    div x13, x25, x26
    div x14, x27, x28
    div x15, x29, x30
    div x16, x31, x1  # x1 is non-zero
    div x17, x2, x3
    div x18, x4, x5
    div x19, x6, x7
    div x20, x8, x9
    div x21, x10, x11
    div x22, x12, x13
    div x23, x14, x15
    div x24, x16, x17
    div x25, x18, x19
    div x26, x20, x21
    div x27, x22, x23
    div x28, x24, x25
    div x29, x26, x27
    div x30, x28, x29
    div x31, x30, x1
    div x1, x2, x3
    div x2, x4, x5
    div x3, x6, x7
    div x4, x8, x9
    div x5, x10, x11
    div x6, x12, x13
    div x7, x14, x15
    div x8, x16, x17
    div x9, x18, x19
    div x10, x20, x21
    div x11, x22, x23
    div x12, x24, x25
    div x13, x26, x27
    div x14, x28, x29
    div x15, x30, x31
    div x16, x1, x2
    div x17, x3, x4
    div x18, x5, x6
    div x19, x7, x8
    div x20, x9, x10
    div x21, x11, x12
    div x22, x13, x14
    div x23, x15, x16
    div x24, x17, x18
    div x25, x19, x20
    div x26, x21, x22
    div x27, x23, x24
    div x28, x25, x26
    div x29, x27, x28
    div x30, x29, x30
    div x31, x31, x1
    # ---------------------------
    # Series of Logical Instructions
    # ---------------------------

    # 'and' instructions
    and x1, x1, x2
    and x2, x3, x4
    and x3, x5, x6
    and x4, x7, x8
    and x5, x9, x10
    and x6, x11, x12
    and x7, x13, x14
    and x8, x15, x16
    and x9, x17, x18
    and x10, x19, x20
    and x11, x21, x22
    and x12, x23, x24
    and x13, x25, x26
    and x14, x27, x28
    and x15, x29, x30
    and x16, x31, x1

    # 'or' instructions
    or x17, x2, x3
    or x18, x4, x5
    or x19, x6, x7
    or x20, x8, x9
    or x21, x10, x11
    or x22, x12, x13
    or x23, x14, x15
    or x24, x16, x17
    or x25, x18, x19
    or x26, x20, x21
    or x27, x22, x23
    or x28, x24, x25
    or x29, x26, x27
    or x30, x28, x29
    or x31, x30, x1

    # 'xor' instructions
    xor x1, x2, x3
    xor x2, x4, x5
    xor x3, x6, x7
    xor x4, x8, x9
    xor x5, x10, x11
    xor x6, x12, x13
    xor x7, x14, x15
    xor x8, x16, x17
    xor x9, x18, x19
    xor x10, x20, x21
    xor x11, x22, x23
    xor x12, x24, x25
    xor x13, x26, x27
    xor x14, x28, x29
    xor x15, x30, x31
    xor x16, x1, x2

    # ---------------------------
    # Series of Shift Instructions
    # ---------------------------

    # 'sll' instructions (Shift Left Logical)
    sll x17, x3, x4
    sll x18, x5, x6
    sll x19, x7, x8
    sll x20, x9, x10
    sll x21, x11, x12
    sll x22, x13, x14
    sll x23, x15, x16
    sll x24, x17, x18
    sll x25, x19, x20
    sll x26, x21, x22
    sll x27, x23, x24
    sll x28, x25, x26
    sll x29, x27, x28
    sll x30, x29, x30
    sll x31, x31, x1

    # 'srl' instructions (Shift Right Logical)
    srl x1, x2, x3
    srl x2, x4, x5
    srl x3, x6, x7
    srl x4, x8, x9
    srl x5, x10, x11
    srl x6, x12, x13
    srl x7, x14, x15
    srl x8, x16, x17
    srl x9, x18, x19
    srl x10, x20, x21
    srl x11, x22, x23
    srl x12, x24, x25
    srl x13, x26, x27
    srl x14, x28, x29
    srl x15, x30, x31
    srl x16, x1, x2

    # 'sra' instructions (Shift Right Arithmetic)
    sra x17, x3, x4
    sra x18, x5, x6
    sra x19, x7, x8
    sra x20, x9, x10
    sra x21, x11, x12
    sra x22, x13, x14
    sra x23, x15, x16
    sra x24, x17, x18
    sra x25, x19, x20
    sra x26, x21, x22
    sra x27, x23, x24
    sra x28, x25, x26
    sra x29, x27, x28
    sra x30, x29, x30
    sra x31, x31, x1

    # ---------------------------
    # Series of Set Less Than Instructions
    # ---------------------------

    # 'slt' instructions
    slt x1, x1, x2
    slt x2, x3, x4
    slt x3, x5, x6
    slt x4, x7, x8
    slt x5, x9, x10
    slt x6, x11, x12
    slt x7, x13, x14
    slt x8, x15, x16
    slt x9, x17, x18
    slt x10, x19, x20
    slt x11, x21, x22
    slt x12, x23, x24
    slt x13, x25, x26
    slt x14, x27, x28
    slt x15, x29, x30
    slt x16, x31, x1

    # ---------------------------
    # Load Floating-Point Registers with Values
    # ---------------------------

    # Prepare data for floating-point registers
    la x1, float_data_array   # Load address of float_data_array into x1

    # Load floating-point registers f0 to f31 with values
    flw f0, 0(x1)
    flw f1, 4(x1)
    flw f2, 8(x1)
    flw f3, 12(x1)
    flw f4, 16(x1)
    flw f5, 20(x1)
    flw f6, 24(x1)
    flw f7, 28(x1)
    flw f8, 32(x1)
    flw f9, 36(x1)
    flw f10, 40(x1)
    flw f11, 44(x1)
    flw f12, 48(x1)
    flw f13, 52(x1)
    flw f14, 56(x1)
    flw f15, 60(x1)
    flw f16, 64(x1)
    flw f17, 68(x1)
    flw f18, 72(x1)
    flw f19, 76(x1)
    flw f20, 80(x1)
    flw f21, 84(x1)
    flw f22, 88(x1)
    flw f23, 92(x1)
    flw f24, 96(x1)
    flw f25, 100(x1)
    flw f26, 104(x1)
    flw f27, 108(x1)
    flw f28, 112(x1)
    flw f29, 116(x1)
    flw f30, 120(x1)
    flw f31, 124(x1)

    # ---------------------------
    # Series of Floating-Point Instructions
    # ---------------------------

    # # 'fadd.s' instructions
    # fadd.s f0, f0, f1
    # fadd.s f1, f2, f3
    # fadd.s f2, f4, f5
    # fadd.s f3, f6, f7
    # fadd.s f4, f8, f9
    # fadd.s f5, f10, f11
    # fadd.s f6, f12, f13
    # fadd.s f7, f14, f15
    # fadd.s f8, f16, f17
    # fadd.s f9, f18, f19
    # fadd.s f10, f20, f21
    # fadd.s f11, f22, f23
    # fadd.s f12, f24, f25
    # fadd.s f13, f26, f27
    # fadd.s f14, f28, f29
    # fadd.s f15, f30, f31

    # # 'fsub.s' instructions
    # fsub.s f16, f0, f1
    # fsub.s f17, f2, f3
    # fsub.s f18, f4, f5
    # fsub.s f19, f6, f7
    # fsub.s f20, f8, f9
    # fsub.s f21, f10, f11
    # fsub.s f22, f12, f13
    # fsub.s f23, f14, f15
    # fsub.s f24, f16, f17
    # fsub.s f25, f18, f19
    # fsub.s f26, f20, f21
    # fsub.s f27, f22, f23
    # fsub.s f28, f24, f25
    # fsub.s f29, f26, f27
    # fsub.s f30, f28, f29
    # fsub.s f31, f30, f0

    # # 'fmul.s' instructions
    # fmul.s f0, f0, f1
    # fmul.s f1, f2, f3
    # fmul.s f2, f4, f5
    # fmul.s f3, f6, f7
    # fmul.s f4, f8, f9
    # fmul.s f5, f10, f11
    # fmul.s f6, f12, f13
    # fmul.s f7, f14, f15
    # fmul.s f8, f16, f17
    # fmul.s f9, f18, f19
    # fmul.s f10, f20, f21
    # fmul.s f11, f22, f23
    # fmul.s f12, f24, f25
    # fmul.s f13, f26, f27
    # fmul.s f14, f28, f29
    # fmul.s f15, f30, f31

    # # 'fdiv.s' instructions
    # fdiv.s f16, f0, f1
    # fdiv.s f17, f2, f3
    # fdiv.s f18, f4, f5
    # fdiv.s f19, f6, f7
    # fdiv.s f20, f8, f9
    # fdiv.s f21, f10, f11
    # fdiv.s f22, f12, f13
    # fdiv.s f23, f14, f15
    # fdiv.s f24, f16, f17
    # fdiv.s f25, f18, f19
    # fdiv.s f26, f20, f21
    # fdiv.s f27, f22, f23
    # fdiv.s f28, f24, f25
    # fdiv.s f29, f26, f27
    # fdiv.s f30, f28, f29
    # fdiv.s f31, f30, f0

    # # Additional Floating-Point Instructions

    # # 'fmadd.s' instructions (Fused Multiply-Add)
    # fmadd.s f0, f1, f2, f3
    # fmadd.s f1, f4, f5, f6
    # fmadd.s f2, f7, f8, f9
    # fmadd.s f3, f10, f11, f12
    # fmadd.s f4, f13, f14, f15
    # fmadd.s f5, f16, f17, f18
    # fmadd.s f6, f19, f20, f21
    # fmadd.s f7, f22, f23, f24
    # fmadd.s f8, f25, f26, f27
    # fmadd.s f9, f28, f29, f30

    # # Floating-Point Comparisons
    # feq.s x1, f1, f2       # x1 = (f1 == f2)
    # flt.s x2, f3, f4       # x2 = (f3 < f4)
    # fle.s x3, f5, f6       # x3 = (f5 <= f6)

    # # Floating-Point Square Roots
    # fsqrt.s f10, f1
    # fsqrt.s f11, f2
    # fsqrt.s f12, f3
    # fsqrt.s f13, f4

    # # Floating-Point Min and Max
    # fmin.s f14, f5, f6
    # fmax.s f15, f7, f8

    # # Floating-Point Absolute Value and Negate
    # fabs.s f16, f9
    # fneg.s f17, f10

    # ---------------------------
    # Load Vector Registers with Values
    # ---------------------------

    # Configure vector unit with correct syntax
    li x1, 0                  # x1 = 0
    vsetvli x0, x1, e32,m8,ta,mu  # Set vector length to maximum for e32 (32-bit elements)

    # Prepare data for vector registers
    la x2, vector_data_array

    # Load vector registers v0 to v7 with values
    vle32.v v0, (x2)
    addi x2, x2, 32            # Advance pointer by 8 elements * 4 bytes
    vle32.v v1, (x2)
    addi x2, x2, 32
    vle32.v v2, (x2)
    addi x2, x2, 32
    vle32.v v3, (x2)
    addi x2, x2, 32
    vle32.v v4, (x2)
    addi x2, x2, 32
    vle32.v v5, (x2)
    addi x2, x2, 32
    vle32.v v6, (x2)
    addi x2, x2, 32
    vle32.v v7, (x2)

    # ---------------------------
    # Series of Vector Instructions
    # ---------------------------

    # 'vadd.vv' instructions
    vadd.vv v8, v0, v1
    vadd.vv v9, v2, v3
    vadd.vv v10, v4, v5
    vadd.vv v11, v6, v7
    vadd.vv v12, v8, v9
    vadd.vv v13, v10, v11
    vadd.vv v14, v12, v13

    # 'vmul.vv' instructions
    vmul.vv v15, v0, v1
    vmul.vv v16, v2, v3
    vmul.vv v17, v4, v5
    vmul.vv v18, v6, v7
    vmul.vv v19, v15, v16
    vmul.vv v20, v17, v18
    vmul.vv v21, v19, v20

    # ---------------------------
    # Series of Vector Floating-Point Operations
    # ---------------------------

    # Load scalar floating-point values into registers
    la t0, float_two
    flw fa0, 0(t0)   # Load 2.0 into fa0
    la t1, float_one
    flw fa1, 0(t1)   # Load 1.0 into fa1
    la t2, float_three
    flw fa2, 0(t2)   # Load 3.0 into fa2
    la t3, float_four
    flw fa3, 0(t3)   # Load 4.0 into fa3

    # 'vfadd.vf' instruction
    vfadd.vf v9, v8, fa0       # v9 = v8 + 2.0
    vfsub.vf v10, v9, fa1      # v10 = v9 - 1.0
    vfmul.vf v11, v10, fa2     # v11 = v10 * 3.0
    vfdiv.vf v12, v11, fa0     # v12 = v11 / 2.0

    # Corrected 'vfmacc.vf' instruction
    vmv.v.v v13, v1            # Initialize v13 with contents of v1
    # vfmacc.vf v13, v12, fa3    # v13 = v13 + (v12 * 4.0)

    # 'vfmv.v.f' instruction
    vfmv.v.f v15, fa0          # Move scalar fa0 into all elements of v15

    # ---------------------------
    # Store Vector Registers
    # ---------------------------

    # Prepare storage location
    la x2, vector_result_array

    # Store vector registers v8 to v21
    vse32.v v8, (x2)
    addi x2, x2, 32
    vse32.v v9, (x2)
    addi x2, x2, 32
    vse32.v v10, (x2)
    addi x2, x2, 32
    vse32.v v11, (x2)
    addi x2, x2, 32
    vse32.v v12, (x2)
    addi x2, x2, 32
    vse32.v v13, (x2)
    addi x2, x2, 32
    vse32.v v14, (x2)
    addi x2, x2, 32
    vse32.v v15, (x2)
    addi x2, x2, 32
    vse32.v v16, (x2)
    addi x2, x2, 32
    vse32.v v17, (x2)
    addi x2, x2, 32
    vse32.v v18, (x2)
    addi x2, x2, 32
    vse32.v v19, (x2)
    addi x2, x2, 32
    vse32.v v20, (x2)
    addi x2, x2, 32
    vse32.v v21, (x2)

    # ---------------------------
    # End of Program
    # ---------------------------

    # Exit the program
    # wfi

    # ---------------------------
    # Data Section
    # ---------------------------

    .section .data

data_array:
    .quad 0x1000000010000000
    .quad 0x2000000020000000
    .quad 0x3000000030000000
    .quad 0x4000000040000000
    .quad 0x5000000050000000
    .quad 0x6000000060000000
    .quad 0x7000000070000000
    .quad 0x8000000080000000
    .quad 0x9000000090000000
    .quad 0xA0000000A0000000
    .quad 0xB0000000B0000000
    .quad 0xC0000000C0000000
    .quad 0xD0000000D0000000
    .quad 0xE0000000E0000000
    .quad 0xF0000000F0000000
    .quad 0x1000000010000001
    .quad 0x1100000011000001
    .quad 0x1200000012000001
    .quad 0x1300000013000001
    .quad 0x1400000014000001
    .quad 0x1500000015000001
    .quad 0x1600000016000001
    .quad 0x1700000017000001
    .quad 0x1800000018000001
    .quad 0x1900000019000001
    .quad 0x1A0000001A000001
    .quad 0x1B0000001B000001
    .quad 0x1C0000001C000001
    .quad 0x1D0000001D000001
    .quad 0x1E0000001E000001
    .quad 0x1F0000001F000001
    .quad 0x2000000020000002
    # Additional data to support the extra load/store instructions
    .space 256        # Allocate extra space for data

float_data_array:
    .float 1.0
    .float 2.0
    .float 3.0
    .float 4.0
    .float 5.0
    .float 6.0
    .float 7.0
    .float 8.0
    .float 9.0
    .float 10.0
    .float 11.0
    .float 12.0
    .float 13.0
    .float 14.0
    .float 15.0
    .float 16.0
    .float 17.0
    .float 18.0
    .float 19.0
    .float 20.0
    .float 21.0
    .float 22.0
    .float 23.0
    .float 24.0
    .float 25.0
    .float 26.0
    .float 27.0
    .float 28.0
    .float 29.0
    .float 30.0
    .float 31.0
    .float 32.0
    .float 33.0
    .float 34.0
    .float 35.0
    .float 36.0
    .float 37.0
    .float 38.0
    .float 39.0
    .float 40.0

float_two:
    .float 2.0
float_one:
    .float 1.0
float_three:
    .float 3.0
float_four:
    .float 4.0

vector_data_array:
    .word 1, 2, 3, 4, 5, 6, 7, 8       # Data for v0
    .word 9, 10, 11, 12, 13, 14, 15, 16  # Data for v1
    .word 17, 18, 19, 20, 21, 22, 23, 24 # Data for v2
    .word 25, 26, 27, 28, 29, 30, 31, 32 # Data for v3
    .word 33, 34, 35, 36, 37, 38, 39, 40 # Data for v4
    .word 41, 42, 43, 44, 45, 46, 47, 48 # Data for v5
    .word 49, 50, 51, 52, 53, 54, 55, 56 # Data for v6
    .word 57, 58, 59, 60, 61, 62, 63, 64 # Data for v7

vector_result_array:
    .space 1024        # Allocate space for vector results
