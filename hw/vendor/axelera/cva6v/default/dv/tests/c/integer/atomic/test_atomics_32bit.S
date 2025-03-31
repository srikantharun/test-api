.option norvc                # Disable RVC if not supported
.option arch, +a             # Enable the 'A' (Atomic) extension

    .section ".text.run_atomics_32b_tests", "ax", @progbits
    .globl run_atomics_32b_tests

run_atomics_32b_tests:
    ########################################################################
    # Setup
    ########################################################################
    la t0, _atomic_data       # Base address for atomic data
    la t1, _atomic_result     # Base address for storing results

    ########################################################################
    # Macro: TEST_AMO_W_LOOP
    #  - 32-bit atomic instructions with optional .aq, .rl, .aqrl
    #  - Excludes x0..x7 (which include ra/sp/t0/t1/t2/etc.) to avoid corruption
    ########################################################################
    .macro TEST_AMO_W_LOOP instr, base_offset
        .set offset, \base_offset

        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                         x16,x17,x18,x19,x20,x21,x22,x23, \
                         x24,x25,x26,x27,x28,x29,x30,x31
                .irp rs2_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                              x16,x17,x18,x19,x20,x21,x22,x23, \
                              x24,x25,x26,x27,x28,x29,x30,x31

                    .irp test_val, 0x7FFFFFFF,0x80000000,0xAAAAAAAA,0x55555555, \
                                   0x00000000,0xFFFFFFFF

                        # 1) Load test_val into rs2_reg
                        li \rs2_reg, \test_val

                        # 2) Initialize memory at (t0) with that value
                        sw \rs2_reg, 0(t0)

                        # 3) Reload rs2_reg
                        li \rs2_reg, \test_val

                        # 4) Perform the atomic instruction
                        \instr\suffix \rd_reg, \rs2_reg, (t0)

                        # 5) Store old memory value (in rd_reg)
                        la  t2, _atomic_result + offset
                        andi t2, t2, -4
                        sw  \rd_reg, 0(t2)

                        # 6) Load updated memory value
                        lw  t5, 0(t0)

                        # 7) Store updated memory value
                        la  t2, _atomic_result + offset + 4
                        andi t2, t2, -4
                        sw  t5, 0(t2)

                        # 8) Bump offset
                        .set offset, offset + 8

                    .endr  # test_val
                .endr      # rs2_reg
            .endr          # rd_reg
        .endr              # suffix
    .endm

    ########################################################################
    # Macro: TEST_LR_SC_W_LOOP
    #  - 32-bit LR/SC with optional .aq, .rl, .aqrl
    #  - Excludes x0..x7 for rd_reg, rs2_reg
    ########################################################################
    .macro TEST_LR_SC_W_LOOP base_offset
        .set offset, \base_offset

        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                         x16,x17,x18,x19,x20,x21,x22,x23, \
                         x24,x25,x26,x27,x28,x29,x30,x31
                .irp rs2_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                              x16,x17,x18,x19,x20,x21,x22,x23, \
                              x24,x25,x26,x27,x28,x29,x30,x31

                    .irp test_val, 0x7FFFFFFF,0x80000000,0xAAAAAAAA, \
                                   0x55555555,0x00000000,0xFFFFFFFF

                        # 1) Initialize memory with test_val
                        li t3, \test_val
                        sw t3, 0(t0)

                        # 2) LR
                        lr.w\suffix \rd_reg, (t0)

                        # 3) Modify the LR result
                        addi \rd_reg, \rd_reg, 1

                        # 4) SC
                        sc.w\suffix t4, \rd_reg, (t0)

                        # 5) Store SC status
                        la  t2, _atomic_result + offset
                        andi t2, t2, -4
                        sw  t4, 0(t2)

                        # 6) Load updated memory value
                        lw  t5, 0(t0)

                        # 7) Store updated memory value
                        la  t2, _atomic_result + offset + 4
                        andi t2, t2, -4
                        sw  t5, 0(t2)

                        # 8) Bump offset
                        .set offset, offset + 8

                    .endr  # test_val
                .endr      # rs2_reg
            .endr          # rd_reg
        .endr              # suffix
    .endm

    ########################################################################
    # Invoke the macros for 32-bit coverage
    ########################################################################

    # Examples:
    TEST_AMO_W_LOOP amoadd.w, 0
    TEST_AMO_W_LOOP amoswap.w, 80000
    TEST_AMO_W_LOOP amoand.w, 160000
    TEST_AMO_W_LOOP amoor.w, 240000
    TEST_AMO_W_LOOP amoxor.w, 320000
    TEST_AMO_W_LOOP amomin.w, 400000
    TEST_AMO_W_LOOP amomax.w, 480000
    TEST_AMO_W_LOOP amominu.w, 560000
    TEST_AMO_W_LOOP amomaxu.w, 640000

    # 32-bit LR/SC
    TEST_LR_SC_W_LOOP 1800000

    ########################################################################
    # Test Completion
    ########################################################################
    ret

    ########################################################################
    # Data Section
    ########################################################################
    .section .data
    .balign 8

    .global _atomic_data
    .balign 8
_atomic_data:
    .dword 0                    # 64-bit slot for our atomic ops

    .global _atomic_result
    .balign 8
_atomic_result:
    .space 2200000             # Adjust size to store your results
