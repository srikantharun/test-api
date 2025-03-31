.option norvc                # Disable RVC if not supported
.option arch, +a             # Enable the 'A' (Atomic) extension
# If you are on RV64, typically you'd have arch rv64g or so,
# but this depends on your environment.

    .section ".text.run_atomics_64b_tests", "ax", @progbits
    .globl run_atomics_64b_tests

run_atomics_64b_tests:
    ########################################################################
    # Setup
    ########################################################################
    la t0, _atomic_data       # Base address for atomic data
    la t1, _atomic_result     # Base address for storing results

    ########################################################################
    # Macro: TEST_AMO_D_LOOP
    #  - 64-bit atomic instructions with optional .aq, .rl, .aqrl
    #  - Excludes x0..x7  (which include ra/sp/t0/t1/t2/etc.) to avoid corruption
    ########################################################################
    .macro TEST_AMO_D_LOOP instr, base_offset
        .set offset, \base_offset

        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                         x16,x17,x18,x19,x20,x21,x22,x23, \
                         x24,x25,x26,x27,x28,x29,x30,x31
                .irp rs2_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                              x16,x17,x18,x19,x20,x21,x22,x23, \
                              x24,x25,x26,x27,x28,x29,x30,x31

                    .irp test_val, 0x7FFFFFFFFFFFFFFF,0x8000000000000000, \
                                   0xAAAAAAAAAAAAAAAA,0x5555555555555555, \
                                   0x0000000000000000,0xFFFFFFFFFFFFFFFF

                        # 1) Load test value into rs2_reg
                        li \rs2_reg, \test_val

                        # 2) Initialize memory at (t0)
                        sd \rs2_reg, 0(t0)

                        # 3) Reload rs2_reg
                        li \rs2_reg, \test_val

                        # 4) Perform the atomic instruction
                        \instr\suffix \rd_reg, \rs2_reg, (t0)

                        # 5) Store old memory value (rd_reg)
                        la  t2, _atomic_result + offset
                        andi t2, t2, -8
                        sd  \rd_reg, 0(t2)

                        # 6) Load updated memory value
                        ld  t5, 0(t0)

                        # 7) Store updated memory value
                        la  t2, _atomic_result + offset + 8
                        andi t2, t2, -8
                        sd  t5, 0(t2)

                        # 8) Bump offset
                        .set offset, offset + 16

                    .endr  # test_val
                .endr      # rs2_reg
            .endr          # rd_reg
        .endr              # suffix
    .endm

    ########################################################################
    # Macro: TEST_LR_SC_D_LOOP
    #  - 64-bit LR/SC instructions with optional .aq, .rl, .aqrl
    #  - Excludes x0..x7
    ########################################################################
    .macro TEST_LR_SC_D_LOOP base_offset
        .set offset, \base_offset

        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                         x16,x17,x18,x19,x20,x21,x22,x23, \
                         x24,x25,x26,x27,x28,x29,x30,x31
                .irp rs2_reg, x8,x9,x10,x11,x12,x13,x14,x15,   \
                              x16,x17,x18,x19,x20,x21,x22,x23, \
                              x24,x25,x26,x27,x28,x29,x30,x31

                    .irp test_val, 0x7FFFFFFFFFFFFFFF,0x8000000000000000, \
                                   0xAAAAAAAAAAAAAAAA,0x5555555555555555, \
                                   0x0000000000000000,0xFFFFFFFFFFFFFFFF

                        # 1) Initialize memory with test_val
                        li t3, \test_val
                        sd t3, 0(t0)

                        # 2) LR
                        lr.d\suffix \rd_reg, (t0)

                        # 3) Modify LR result
                        addi \rd_reg, \rd_reg, 1

                        # 4) SC
                        sc.d\suffix t4, \rd_reg, (t0)

                        # 5) Store SC status
                        la  t2, _atomic_result + offset
                        andi t2, t2, -8
                        sw  t4, 0(t2)

                        # 6) Load updated memory value
                        ld  t5, 0(t0)

                        # 7) Store updated memory value
                        la  t2, _atomic_result + offset + 8
                        andi t2, t2, -8
                        sd  t5, 0(t2)

                        # 8) Bump offset
                        .set offset, offset + 16

                    .endr  # test_val
                .endr      # rs2_reg
            .endr          # rd_reg
        .endr              # suffix
    .endm

    ########################################################################
    # Invoke the macros for 64-bit coverage
    ########################################################################

    # 64-bit AMOs
    TEST_AMO_D_LOOP amoadd.d,   720000
    TEST_AMO_D_LOOP amoswap.d,  840000
    TEST_AMO_D_LOOP amoand.d,   960000
    TEST_AMO_D_LOOP amoor.d,    1080000
    TEST_AMO_D_LOOP amoxor.d,   1200000
    TEST_AMO_D_LOOP amomin.d,   1320000
    TEST_AMO_D_LOOP amomax.d,   1440000
    TEST_AMO_D_LOOP amominu.d,  1560000
    TEST_AMO_D_LOOP amomaxu.d,  1680000

    # 64-bit LR/SC
    TEST_LR_SC_D_LOOP 2000000

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
