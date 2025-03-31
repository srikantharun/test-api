.option norvc                # Disable RVC if not supported
.option arch, +a             # Enable the 'A' (Atomic) extension

    .section ".text.run_atomic_tests", "ax", @progbits
    .globl run_atomic_tests

run_atomic_tests:
    #-----------------------------------------------------------
    # Setup
    #-----------------------------------------------------------
    # Initialize test data addresses
    la t0, _atomic_data       # Base address for atomic data
    la t1, _atomic_result     # Base address for storing results

    #-----------------------------------------------------------
    # Macro Definitions
    #-----------------------------------------------------------

    # Macro to generate tests for 32-bit atomic instructions with suffixes
    .macro TEST_AMO_W_LOOP instr, base_offset
        .set offset, \base_offset
        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x9,x18,x19,x20,x21,x22,x23  # s1-s7 (avoid t0-t6)
                .irp rs2_reg, x18,x19,x20,x21,x22,x23  # s2-s7 (avoid t0-t6)
                    .irp test_val, 0x7FFFFFFF,0x80000000,0xAAAAAAAA,0x55555555,0x00000000,0xFFFFFFFF
                        # Load test value into rs2_reg
                        li \rs2_reg, \test_val
                        # Store initial memory value (aligned address)
                        sw \rs2_reg, 0(t0)
                        # Load rs2 value
                        li \rs2_reg, \test_val
                        # Perform the atomic instruction with suffix
                        \instr\suffix \rd_reg, \rs2_reg, (t0)
                        # Store results
                        # Compute effective address for storing rd_reg
                        la t2, _atomic_result + offset
                        # Ensure address is aligned to 4 bytes
                        andi t2, t2, -4
                        sw \rd_reg, 0(t2)
                        # Load updated memory value
                        lw t5, 0(t0)
                        # Compute address for storing t5
                        la t2, _atomic_result + offset + 4
                        # Ensure address is aligned to 4 bytes
                        andi t2, t2, -4
                        sw t5, 0(t2)
                        # Increment offset for next result
                        .set offset, offset + 8
                    .endr
                .endr
            .endr
        .endr
    .endm

    # Macro to generate tests for 64-bit atomic instructions with suffixes
    .macro TEST_AMO_D_LOOP instr, base_offset
        .set offset, \base_offset
        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x9,x18,x19,x20,x21,x22,x23  # s1-s7 (avoid t0-t6)
                .irp rs2_reg, x18,x19,x20,x21,x22,x23  # s2-s7 (avoid t0-t6)
                    .irp test_val, 0x7FFFFFFFFFFFFFFF,0x8000000000000000, \
                        0xAAAAAAAAAAAAAAAA,0x5555555555555555, \
                        0x0000000000000000,0xFFFFFFFFFFFFFFFF
                        # Load test value into rs2_reg
                        li \rs2_reg, \test_val
                        # Store initial memory value (aligned address)
                        sd \rs2_reg, 0(t0)
                        # Load rs2 value
                        li \rs2_reg, \test_val
                        # Perform the atomic instruction with suffix
                        \instr\suffix \rd_reg, \rs2_reg, (t0)
                        # Store results
                        # Compute effective address for storing rd_reg
                        la t2, _atomic_result + offset
                        # Ensure address is aligned to 8 bytes
                        andi t2, t2, -8
                        sd \rd_reg, 0(t2)
                        # Load updated memory value
                        ld t5, 0(t0)
                        # Compute address for storing t5
                        la t2, _atomic_result + offset + 8
                        # Ensure address is aligned to 8 bytes
                        andi t2, t2, -8
                        sd t5, 0(t2)
                        # Increment offset for next result
                        .set offset, offset + 16
                    .endr
                .endr
            .endr
        .endr
    .endm

    # Macro to generate tests for 32-bit LR/SC instructions with suffixes
    .macro TEST_LR_SC_W_LOOP base_offset
        .set offset, \base_offset
        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x9,x18,x19,x20,x21,x22,x23  # s1-s7
                .irp rs2_reg, x18,x19,x20,x21,x22,x23  # s2-s7
                    .irp test_val, 0x7FFFFFFF,0x80000000,0xAAAAAAAA,0x55555555,0x00000000,0xFFFFFFFF
                        # Initialize memory with test value
                        li t3, \test_val
                        sw t3, 0(t0)
                        # Perform LR instruction
                        lr.w\suffix \rd_reg, (t0)
                        # Modify the value in rd_reg (e.g., add 1)
                        addi \rd_reg, \rd_reg, 1
                        # Attempt SC instruction
                        sc.w\suffix t4, \rd_reg, (t0)
                        # Store results
                        # Compute effective address for storing status from SC
                        la t2, _atomic_result + offset
                        # Ensure address is aligned to 4 bytes
                        andi t2, t2, -4
                        sw t4, 0(t2)   # Store SC status (0 = success, non-zero = failure)
                        # Load updated memory value
                        lw t5, 0(t0)
                        # Compute address for storing t5
                        la t2, _atomic_result + offset + 4
                        # Ensure address is aligned to 4 bytes
                        andi t2, t2, -4
                        sw t5, 0(t2)
                        # Increment offset for next result
                        .set offset, offset + 8
                    .endr
                .endr
            .endr
        .endr
    .endm

    # Macro to generate tests for 64-bit LR/SC instructions with suffixes
    .macro TEST_LR_SC_D_LOOP base_offset
        .set offset, \base_offset
        .irp suffix, , .aq, .rl, .aqrl
            .irp rd_reg, x9,x18,x19,x20,x21,x22,x23  # s1-s7
                .irp rs2_reg, x18,x19,x20,x21,x22,x23  # s2-s7
                    .irp test_val, 0x7FFFFFFFFFFFFFFF,0x8000000000000000, \
                        0xAAAAAAAAAAAAAAAA,0x5555555555555555, \
                        0x0000000000000000,0xFFFFFFFFFFFFFFFF
                        # Initialize memory with test value
                        li t3, \test_val
                        sd t3, 0(t0)
                        # Perform LR instruction
                        lr.d\suffix \rd_reg, (t0)
                        # Modify the value in rd_reg (e.g., add 1)
                        addi \rd_reg, \rd_reg, 1
                        # Attempt SC instruction
                        sc.d\suffix t4, \rd_reg, (t0)
                        # Store results
                        # Compute effective address for storing status from SC
                        la t2, _atomic_result + offset
                        # Ensure address is aligned to 8 bytes
                        andi t2, t2, -8
                        sw t4, 0(t2)   # Store SC status (0 = success, non-zero = failure)
                        # Load updated memory value
                        ld t5, 0(t0)
                        # Compute address for storing t5
                        la t2, _atomic_result + offset + 8
                        # Ensure address is aligned to 8 bytes
                        andi t2, t2, -8
                        sd t5, 0(t2)
                        # Increment offset for next result
                        .set offset, offset + 16
                    .endr
                .endr
            .endr
        .endr
    .endm

    #-----------------------------------------------------------
    # Testing All AMO Instructions with Loops and Suffixes
    #-----------------------------------------------------------

    # AMOADD.W Tests
    TEST_AMO_W_LOOP amoadd.w, 0

    # AMOSWAP.W Tests
    TEST_AMO_W_LOOP amoswap.w, 80000

    # AMOAND.W Tests
    TEST_AMO_W_LOOP amoand.w, 160000

    # AMOOR.W Tests
    TEST_AMO_W_LOOP amoor.w, 240000

    # AMOXOR.W Tests
    TEST_AMO_W_LOOP amoxor.w, 320000

    # AMOMIN.W Tests
    TEST_AMO_W_LOOP amomin.w, 400000

    # AMOMAX.W Tests
    TEST_AMO_W_LOOP amomax.w, 480000

    # AMOMINU.W Tests
    TEST_AMO_W_LOOP amominu.w, 560000

    # AMOMAXU.W Tests
    TEST_AMO_W_LOOP amomaxu.w, 640000

    # AMOADD.D Tests
    TEST_AMO_D_LOOP amoadd.d, 720000

    # AMOSWAP.D Tests
    TEST_AMO_D_LOOP amoswap.d, 840000

    # AMOAND.D Tests
    TEST_AMO_D_LOOP amoand.d, 960000

    # AMOOR.D Tests
    TEST_AMO_D_LOOP amoor.d, 1080000

    # AMOXOR.D Tests
    TEST_AMO_D_LOOP amoxor.d, 1200000

    # AMOMIN.D Tests
    TEST_AMO_D_LOOP amomin.d, 1320000

    # AMOMAX.D Tests
    TEST_AMO_D_LOOP amomax.d, 1440000

    # AMOMINU.D Tests
    TEST_AMO_D_LOOP amominu.d, 1560000

    # AMOMAXU.D Tests
    TEST_AMO_D_LOOP amomaxu.d, 1680000

    #-----------------------------------------------------------
    # Testing LR/SC Instructions with Loops and Suffixes
    #-----------------------------------------------------------

    # LR.W/SC.W Tests
    TEST_LR_SC_W_LOOP 1800000

    # LR.D/SC.D Tests
    TEST_LR_SC_D_LOOP 2000000

    #-----------------------------------------------------------
    # Test Completion
    #-----------------------------------------------------------
    ret

    #-----------------------------------------------------------
    # Data Section
    #-----------------------------------------------------------
    .section .data
    .balign 8                   # Align to 8 bytes for 64-bit data

    .global _atomic_data
    .balign 8                   # Ensure _atomic_data is 8-byte aligned
_atomic_data:
    .dword 0                   # Memory location for atomic operations (64-bit)

    .global _atomic_result
    .balign 8                   # Ensure _atomic_result is 8-byte aligned
_atomic_result:
    .space 2200000               # Adjust size based on total number of tests
