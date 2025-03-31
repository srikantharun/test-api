.section ".text.run_missed_vector_tests", "ax", @progbits
.globl run_missed_vector_tests

run_missed_vector_tests:
    #-----------------------------------------------------------
    # Setup
    #-----------------------------------------------------------
    # Initialize vector unit
    li t0, 0
    vsetvli t0, t0, e32, m1, tu, mu  # Set SEW=32, LMUL=1

    # Initialize mask register v0 to all ones
    li t0, -1
    vmv.v.x v0, t0

    #-----------------------------------------------------------
    # Macro Definitions
    #-----------------------------------------------------------

    # Macro for integer extension instructions
    .macro TEST_VECTOR_VV_LOOP_INT_EXT instr
        .irp vd_reg, v1,v2,v3,v4
            .irp vs2_reg, v5,v6,v7,v8
                # Set SEW and LMUL for source and destination
                vsetvli t0, t0, e16, m1, tu, mu  # SEW=16 for source
                # Initialize source vector register vs2
                li t1, 0x0101
                vmv.v.x \vs2_reg, t1

                vsetvli t0, t0, e32, m1, tu, mu  # SEW=32 for destination

                # Execute the instruction with mask operand
                \instr \vd_reg, \vs2_reg, v0.t

                # Optionally store the result for verification

            .endr
        .endr
    .endm

    # Macro for integer vector-vector instructions (three operands)
    .macro TEST_VECTOR_VV_LOOP_INT instr
        .irp vd_reg, v1,v2,v3,v4
            .irp vs1_reg, v5,v6,v7,v8
                .irp vs2_reg, v9,v10,v11,v12
                    # Initialize vector registers with integer test data
                    li t1, 0x01010101
                    vmv.v.x \vd_reg, t1
                    li t2, 0x02020202
                    vmv.v.x \vs1_reg, t2
                    li t3, 0x03030303
                    vmv.v.x \vs2_reg, t3

                    # Execute the instruction
                    \instr \vd_reg, \vs1_reg, \vs2_reg

                    # Optionally store the result for verification

                .endr
            .endr
        .endr
    .endm

    # # Macro for integer vector instructions (two operands)
    # .macro TEST_VECTOR_VV_LOOP_INT_2OP instr
    #     .irp vd_reg, v1,v2,v3,v4,v5,v6,v7,v8,v9
    #         .irp vs2_reg, v10,v11,v12,v13,v14,v15,v16,v17,v18
    #             # Initialize vector registers with integer test data
    #             li t1, 0x01010101
    #             vmv.v.x \vd_reg, t1
    #             li t3, 0x03030303
    #             vmv.v.x \vs2_reg, t3

    #             # Execute the instruction
    #             \instr \vd_reg, \vs2_reg

    #             # Optionally store the result for verification

    #         .endr
    #     .endr
    # .endm

    # Macro for floating-point vector-vector instructions
    .macro TEST_VECTOR_VV_LOOP_FP instr
        .irp vd_reg, v1,v2,v3,v4,v5,v6,v7,v8,v9
            .irp vs1_reg, v10,v11,v12,v13,v14,v15,v16,v17,v18
                .irp vs2_reg, v19,v20,v21,v22,v23,v24,v25,v26,v27
                    # Initialize vector registers with floating-point test data
                    la t0, float_one
                    flw f0, 0(t0)
                    vfmv.v.f \vd_reg, f0

                    la t0, float_two
                    flw f1, 0(t0)
                    vfmv.v.f \vs1_reg, f1

                    la t0, float_three
                    flw f2, 0(t0)
                    vfmv.v.f \vs2_reg, f2

                    # Execute the instruction
                    \instr \vd_reg, \vs1_reg, \vs2_reg

                    # Optionally store the result for verification

                .endr
            .endr
        .endr
    .endm

    # Macro for floating-point vector-scalar instructions
    .macro TEST_VECTOR_VF_LOOP_FP instr
        .irp vd_reg, v1,v2,v3,v4,v5,v6,v7,v8,v9
            .irp vs_reg, v10,v11,v12,v13,v14,v15,v16,v17,v18
                .irp rs1_reg, f5,f6,f7,f28,f29,f30,f31
                    # Initialize vector and scalar registers with floating-point test data
                    la t0, float_one
                    flw f0, 0(t0)
                    vfmv.v.f \vd_reg, f0

                    la t0, float_two
                    flw f1, 0(t0)
                    vfmv.v.f \vs_reg, f1

                    la t0, float_three
                    flw \rs1_reg, 0(t0)

                    # Execute the instruction
                    \instr \vd_reg, \vs_reg, \rs1_reg

                    # Optionally store the result for verification

                .endr
            .endr
        .endr
    .endm

    # Macro for floating-point vector reduction instructions
    .macro TEST_VECTOR_REDUCTION_LOOP_FP instr
        .irp vd_reg, v1,v2,v3,v4,v5,v6,v7,v8,v9
            .irp vs1_reg, v10,v11,v12,v13,v14,v15,v16,v17,v18
                # Initialize vector registers with floating-point test data
                la t0, float_one
                flw f0, 0(t0)
                vfmv.v.f \vd_reg, f0

                la t0, float_two
                flw f1, 0(t0)
                vfmv.v.f \vs1_reg, f1

                # Execute the instruction
                \instr \vd_reg, \vd_reg, \vs1_reg

                # Optionally store the result for verification

            .endr
        .endr
    .endm

    # Macro for integer vector reduction instructions
    .macro TEST_VECTOR_REDUCTION_LOOP_INT instr
        .irp vd_reg, v1,v2,v3,v4,v5,v6,v7,v8,v9
            .irp vs1_reg, v10,v11,v12,v13,v14,v15,v16,v17,v18
                # Initialize vector registers with integer test data
                li t1, 0x01010101
                vmv.v.x \vd_reg, t1
                li t2, 0x02020202
                vmv.v.x \vs1_reg, t2

                # Execute the instruction
                \instr \vd_reg, \vd_reg, \vs1_reg

                # Optionally store the result for verification

            .endr
        .endr
    .endm

    # Macro for integer vector-vector instructions (two operands)
    .macro TEST_VECTOR_VV_LOOP_INT_2OP instr
        .irp vd_reg, v1,v2,v3,v4,v5,v6,v7,v8,v9
            .irp vs2_reg, v10,v11,v12,v13,v14,v15,v16,v17,v18
                # Initialize vector registers with integer test data
                li t1, 0x0101
                vmv.v.x \vd_reg, t1
                li t3, 0x0303
                vmv.v.x \vs2_reg, t3

                # Execute the instruction with mask register v0.t
                \instr \vd_reg, \vs2_reg, v0.t

                # Optionally store the result for verification

            .endr
        .endr
    .endm

    # Macro for integer vector-scalar widening multiply-accumulate instructions
# Macro for integer vector-scalar widening multiply-accumulate instructions
.macro TEST_VECTOR_VX_WIDENING_INT instr
    # Set vector length (VL) and width (SEW) for source operands
    vsetvli t0, x0, e16, m1, ta, ma   # SEW=16, LMUL=1

    # Initialize narrow source vector register vs2 (v1)
    li t2, 0x0202
    vmv.v.x v1, t2

    # Initialize scalar source register rs1 (t3)
    li t3, 0x0303

    # Configure for destination with double width (2*SEW)
    vsetvli t0, x0, e32, m2, ta, ma    # SEW=32, LMUL=2 for destination

    # Initialize destination vector register vd (v2)
    vmv.v.i v2, 0

    # Execute widening multiply-accumulate
    # vd[i] = +(x[rs1] * vs2[i]) + vd[i]
    \instr v2, t3, v1
.endm


    #-----------------------------------------------------------
    # Test Instructions
    #-----------------------------------------------------------

    # Floating-point vector-scalar comparisons
    TEST_VECTOR_VF_LOOP_FP vmfle.vf
    TEST_VECTOR_VF_LOOP_FP vmfge.vf
    TEST_VECTOR_VF_LOOP_FP vmfgt.vf
    TEST_VECTOR_VF_LOOP_FP vmflt.vf
    TEST_VECTOR_VF_LOOP_FP vmfne.vf

    # Floating-point vector-vector comparisons
    TEST_VECTOR_VV_LOOP_FP vmfle.vv
    TEST_VECTOR_VV_LOOP_FP vmfne.vv

    # Integer extension instructions
    TEST_VECTOR_VV_LOOP_INT_EXT vsext.vf2
    TEST_VECTOR_VV_LOOP_INT_EXT vzext.vf2

    # Floating-point vector reductions
    TEST_VECTOR_REDUCTION_LOOP_FP vfredmax.vs
    TEST_VECTOR_REDUCTION_LOOP_FP vfredmin.vs
    TEST_VECTOR_REDUCTION_LOOP_FP vfredosum.vs
    TEST_VECTOR_REDUCTION_LOOP_FP vfredsum.vs
    # Widening reductions require special handling (not included here)

    # Integer vector reductions
    TEST_VECTOR_REDUCTION_LOOP_INT vredand.vs
    TEST_VECTOR_REDUCTION_LOOP_INT vredor.vs
    TEST_VECTOR_REDUCTION_LOOP_INT vredxor.vs
    TEST_VECTOR_REDUCTION_LOOP_INT vredsum.vs
    # Widening reductions require special handling (not included here)

    # Integer vector-scalar widening multiply-accumulate instructions
    # TEST_VECTOR_VX_WIDENING_INT vwmacc.vx
    # TEST_VECTOR_VX_WIDENING_INT vwmaccsu.vx
    # TEST_VECTOR_VX_WIDENING_INT vwmaccu.vx
    #-----------------------------------------------------------
    # Test Completion
    #-----------------------------------------------------------
    ret

    #-----------------------------------------------------------
    # Data Section
    #-----------------------------------------------------------
    .section .data
    .align 4

float_one:
    .float 1.0

float_two:
    .float 2.0

float_three:
    .float 3.0
