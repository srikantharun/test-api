// test_frm_asm.S
// Assembly-based test case for 'frm' in 'fcsr' CSR
// Modified to run for all rounding modes
// Author: Abhilash

    .section ".text.run_tests", "ax", @progbits
    .globl run_frm_assembly_tests

run_frm_assembly_tests:
    # Prologue: Save callee-saved registers
    addi sp, sp, -48            # Allocate stack space
    sd ra, 40(sp)
    sd s0, 32(sp)
    sd s1, 24(sp)
    sd s2, 16(sp)
    sd s3, 8(sp)
    sd s4, 0(sp)

    # Initialize pointers and counters
    li s0, 0                     # s0 = rounding mode (0 to 4)
    la s1, result_bits           # s1 = &result_bits
    la s3, expected_results      # s3 = &expected_results
    la s4, result_addition_correct # s4 = &result_addition_correct

loop_start:
    li t0, 5                     # Load immediate value 5 into t0
    blt s0, t0, loop_body        # If s0 < 5, proceed; else, end
    j end_tests

loop_body:
    # Set frm to s0
    slli s2, s0, 5               # Shift s0 left by 5 to position frm bits
    csrw fcsr, s2                # Write s2 to fcsr (frm in bits [7:5])

    # Read back fcsr to verify frm
    csrr a1, fcsr
    srli a1, a1, 5
    andi a1, a1, 0x7
    bne a1, s0, frm_set_incorrect

    # Load operands
    la t1, one_point_one
    flw ft0, 0(t1)
    la t2, one
    flw ft1, 0(t2)

    # Perform Floating-Point Addition
    fadd.s ft2, ft0, ft1

    # Move bits of ft2 into a2
    fmv.x.w a2, ft2

    # Store result bits in result_bits[s0]
    slli t0, s0, 2               # t0 = s0 * 4 (word offset)
    add t1, s1, t0               # t1 = s1 + t0
    sw a2, 0(t1)

    # Load expected result for current rounding mode
    add t2, s3, t0
    lw t3, 0(t2)

    # Compare a2 with expected result
    beq a2, t3, addition_correct

    # If not correct, set result_addition_correct[s0] to 0 (fail)
    li t4, 0
    add t5, s4, t0
    sw t4, 0(t5)
    j increment_s0

addition_correct:
    # If correct, set result_addition_correct[s0] to 1 (pass)
    li t4, 1
    add t5, s4, t0
    sw t4, 0(t5)

increment_s0:
    addi s0, s0, 1               # Increment rounding mode
    j loop_start

frm_set_incorrect:
    # Handle frm set incorrect (should not happen)
    li a2, -1                    # Indicate error in result_bits
    slli t0, s0, 2
    add t1, s1, t0
    sw a2, 0(t1)
    # Also, set result_addition_correct[s0] to 0 (fail)
    li t4, 0
    add t5, s4, t0
    sw t4, 0(t5)
    addi s0, s0, 1               # Increment rounding mode
    j loop_start

end_tests:
    # Epilogue: Restore callee-saved registers
    ld ra, 40(sp)
    ld s0, 32(sp)
    ld s1, 24(sp)
    ld s2, 16(sp)
    ld s3, 8(sp)
    ld s4, 0(sp)
    addi sp, sp, 48
    ret

    # ===============================
    # Data Section for Test Results
    # ===============================
    .section ".data.run_tests", "aw", @progbits
    .globl result_bits
    .globl expected_results
    .globl result_addition_correct

result_bits:
    .space 20                    # Space for 5 words (rounding modes 0 to 4)

expected_results:
    .word 0x40066666             # Expected result for RNE (0b000)
    .word 0x40066666             # Expected result for RTZ (0b001)
    .word 0x40066666             # Expected result for RDN (0b010)
    .word 0x40066667             # Expected result for RUP (0b011)
    .word 0x40066667             # Expected result for RMM (0b100)

result_addition_correct:
    .word 0, 0, 0, 0, 0          # Initialize pass/fail flags for each mode

    # ===============================
    # Read-Only Data Section
    # ===============================
    .section ".rodata.run_tests", "a", @progbits
    .align 2                      # Align to 4-byte boundary
one_point_one:
    .float 1.1
    .align 2                      # Align to 4-byte boundary
one:
    .float 1.0
