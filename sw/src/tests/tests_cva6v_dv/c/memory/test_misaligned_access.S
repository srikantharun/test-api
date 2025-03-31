# misaligned_access_tests.S
# Assembly Test File for Misaligned Access Tests on RISC-V

.section .text.init
.globl run_misaligned_access_tests
.align 4

.section .data
.globl trap_occurred
trap_occurred:
    .word 0

# Macro to check if a bit is set in the test mask
# Usage: CHECK_TEST_BIT bit_number, label_to_jump_if_not_set
.macro CHECK_TEST_BIT bitnum, skip_label
    li      t0, 1
    slli    t0, t0, \bitnum       # t0 = 1 << bitnum
    and     t0, s7, t0            # t0 = test_mask & (1 << bitnum)
    beqz    t0, \skip_label       # If zero, skip the test
.endm

run_misaligned_access_tests:
    # Save callee-saved registers
    addi    sp, sp, -64             # Adjust stack pointer
    sd      s0, 56(sp)
    sd      s1, 48(sp)
    sd      s2, 40(sp)
    sd      s3, 32(sp)
    sd      s4, 24(sp)
    sd      s5, 16(sp)
    sd      s6, 8(sp)
    sd      s7, 0(sp)

    # Save the original mtvec value
    csrr    s0, mtvec               # Save old mtvec into s0

    # Set mtvec to point to the trap handler
    la      t0, trap_handler        # Load address of trap_handler into t0
    csrw    mtvec, t0               # Set mtvec to point to the trap handler

    # The test mask is in a0
    mv      s7, a0                  # Save test_mask in s7 for later use

    # Initialize vector registers
    vsetvli t0, zero, e64, m1, ta, ma  # Set vector length for 64-bit elements

    # -----------------------------------------
    # Test 0: Aligned Instruction Fetch
    # -----------------------------------------
    CHECK_TEST_BIT 0, test_1_misaligned_instr_fetch

    # Expected: Execution continues normally
    la      s0, aligned_instruction_address
    jr      s0                      # Jump to aligned address

aligned_instruction_address:
    .align 4
    addi    t0, zero, 42            # Simple instruction (t0 = 42)
    j       test_1_misaligned_instr_fetch  # Jump to next test

    # -----------------------------------------
    # Test 1: Misaligned Instruction Fetch
    # -----------------------------------------
test_1_misaligned_instr_fetch:
    CHECK_TEST_BIT 1, test_2_aligned_load_store_byte

    # Expected: Instruction address misaligned exception
    la      s0, misaligned_instruction_address
    addi    s0, s0, 1               # Make s0 misaligned
    jalr    zero, 0(s0)             # Attempt to jump to misaligned address

    # Execution resumes here after trap handler adjusts mepc
    j       test_2_aligned_load_store_byte

misaligned_instruction_address:
    .align 2                        # Align to 2-byte boundary
    .word 0x00000013                # NOP instruction (addi x0, x0, 0)

    # -----------------------------------------
    # Test 2: Aligned Load/Store Byte
    # -----------------------------------------
test_2_aligned_load_store_byte:
    CHECK_TEST_BIT 2, test_3_misaligned_load_store_byte

    # Expected: Load/Store succeeds without exception
    la      s0, aligned_data_byte
    lb      t0, 0(s0)               # Load byte from aligned address
    addi    t0, t0, 1               # Increment the byte
    sb      t0, 0(s0)               # Store byte back to aligned address
    j       test_3_misaligned_load_store_byte

    # -----------------------------------------
    # Test 3: Misaligned Load/Store Byte
    # -----------------------------------------
test_3_misaligned_load_store_byte:
    CHECK_TEST_BIT 3, test_4_aligned_load_store_halfword

    # Expected: Load/Store succeeds (bytes can be accessed at any alignment)
    la      s0, misaligned_data_byte
    lb      t0, 1(s0)               # Load byte from misaligned address
    addi    t0, t0, 1               # Increment the byte
    sb      t0, 1(s0)               # Store byte back to misaligned address
    j       test_4_aligned_load_store_halfword

    # -----------------------------------------
    # Test 4: Aligned Load/Store Half-Word
    # -----------------------------------------
test_4_aligned_load_store_halfword:
    CHECK_TEST_BIT 4, test_5_misaligned_load_store_halfword

    # Expected: Load/Store succeeds without exception
    la      s0, aligned_data_half
    lh      t0, 0(s0)               # Load half-word from aligned address
    addi    t0, t0, 1               # Increment the half-word
    sh      t0, 0(s0)               # Store half-word back to aligned address
    j       test_5_misaligned_load_store_halfword

    # -----------------------------------------
    # Test 5: Misaligned Load/Store Half-Word
    # -----------------------------------------
test_5_misaligned_load_store_halfword:
    CHECK_TEST_BIT 5, test_6_aligned_load_store_word

    # Expected: Trap occurs if misaligned accesses not supported
    la      s0, misaligned_data_half
    lh      t0, 1(s0)               # Load half-word from misaligned address
    la      t1, result_misaligned_lh
    sw      t0, 0(t1)               # Store result for checking
    sh      t0, 1(s0)               # Attempt to store to misaligned address
    j       test_6_aligned_load_store_word

    # -----------------------------------------
    # Test 6: Aligned Load/Store Word
    # -----------------------------------------
test_6_aligned_load_store_word:
    CHECK_TEST_BIT 6, test_7_misaligned_load_store_word

    # Expected: Load/Store succeeds without exception
    la      s0, aligned_data_word
    lw      t0, 0(s0)               # Load word from aligned address
    addi    t0, t0, 1               # Increment the word
    sw      t0, 0(s0)               # Store word back to aligned address
    j       test_7_misaligned_load_store_word

    # -----------------------------------------
    # Test 7: Misaligned Load/Store Word
    # -----------------------------------------
test_7_misaligned_load_store_word:
    CHECK_TEST_BIT 7, test_8_aligned_load_store_dword

    # Expected: Trap occurs if misaligned accesses not supported
    la      s0, misaligned_data_word
    lw      t0, 2(s0)               # Load word from misaligned address
    la      t1, result_misaligned_lw
    sw      t0, 0(t1)               # Store result for checking
    sw      t0, 2(s0)               # Attempt to store to misaligned address
    j       test_8_aligned_load_store_dword

    # -----------------------------------------
    # Test 8: Aligned Load/Store Double-Word
    # -----------------------------------------
test_8_aligned_load_store_dword:
    CHECK_TEST_BIT 8, test_9_misaligned_load_store_dword

    # Expected: Load/Store succeeds without exception
    la      s0, aligned_data_dword
    ld      t0, 0(s0)               # Load double-word from aligned address
    addi    t0, t0, 1               # Increment the double-word
    sd      t0, 0(s0)               # Store double-word back to aligned address
    j       test_9_misaligned_load_store_dword

    # -----------------------------------------
    # Test 9: Misaligned Load/Store Double-Word
    # -----------------------------------------
test_9_misaligned_load_store_dword:
    CHECK_TEST_BIT 9, test_10_misaligned_amo

    # Expected: Trap occurs if misaligned accesses not supported
    la      s0, misaligned_data_dword
    ld      t0, 4(s0)               # Load double-word from misaligned address
    la      t1, result_misaligned_ld
    sd      t0, 0(t1)               # Store result for checking
    sd      t0, 4(s0)               # Attempt to store to misaligned address
    j       test_10_misaligned_amo

    # -----------------------------------------
    # Test 10: Misaligned Atomic Operation (AMO)
    # -----------------------------------------
test_10_misaligned_amo:
    CHECK_TEST_BIT 10, test_11_misaligned_lr_sc

    # Expected: Trap occurs due to misaligned address
    la      s0, misaligned_atomic_addr
    addi    s0, s0, 1               # Adjust s0 to misaligned address
    li      t1, 0xCAFEBABE
    amoswap.w.aq t2, t1, (s0)       # Atomic swap on misaligned address
    la      t3, result_misaligned_amo
    sw      t2, 0(t3)               # Store result for checking
    j       test_11_misaligned_lr_sc

    # -----------------------------------------
    # Test 11: Misaligned LR/SC Sequence
    # -----------------------------------------
test_11_misaligned_lr_sc:
    CHECK_TEST_BIT 11, test_12_misaligned_vector_load_store

    # Expected: SC should fail or trap due to misaligned address
    la      s0, misaligned_lrsc_addr
    addi    s0, s0, 3               # Misaligned address
    lr.w    t0, (s0)                # Load-reserved from misaligned address
    addi    t0, t0, 1               # Increment the value
    sc.w    t1, t0, (s0)            # Store-conditional to misaligned address
    la      t2, result_misaligned_lrsc
    sw      t1, 0(t2)               # Store result (t1 == 0 if SC succeeded)
    j       test_12_misaligned_vector_load_store

    # -----------------------------------------
    # Test 12: Misaligned Vector Load/Store
    # -----------------------------------------
test_12_misaligned_vector_load_store:
    CHECK_TEST_BIT 12, test_13_misaligned_fp_load_store

    # Expected: Trap occurs if misaligned accesses not supported
    la      s0, misaligned_vector_data
    vle32.v v0, (s0)                # Load vector from misaligned address
    la      s1, result_misaligned_vl
    vse32.v v0, (s1)                # Store vector for checking
    la      s0, misaligned_vector_data_store
    vse32.v v0, (s0)                # Attempt to store vector to misaligned address
    j       test_13_misaligned_fp_load_store

    # -----------------------------------------
    # Test 13: Misaligned Floating-Point Load/Store
    # -----------------------------------------
test_13_misaligned_fp_load_store:
    CHECK_TEST_BIT 13, test_14_misaligned_page_boundary_access

    # Expected: Trap occurs if misaligned accesses not supported
    la      s0, misaligned_fp_data
    flw     ft0, 1(s0)              # Load float from misaligned address
    fadd.s  ft0, ft0, ft0           # Perform some operation
    fsw     ft0, 1(s0)              # Store float to misaligned address
    la      t0, result_misaligned_flw
    fsw     ft0, 0(t0)              # Store result for checking
    j       test_14_misaligned_page_boundary_access

    # -----------------------------------------
    # Test 14: Misaligned Access Crossing Page Boundary
    # -----------------------------------------
test_14_misaligned_page_boundary_access:
    CHECK_TEST_BIT 14, test_15_misaligned_cache_line_boundary

    # Expected: Access may cause page fault or misaligned exception
    la      s0, page_boundary_data
    addi    s0, s0, -2              # Address so that access crosses page boundary
    lw      t0, 0(s0)               # Load word crossing page boundary
    j       test_15_misaligned_cache_line_boundary

    # -----------------------------------------
    # Test 15: Misaligned Access at Cache Line Boundary
    # -----------------------------------------
test_15_misaligned_cache_line_boundary:
    CHECK_TEST_BIT 15, test_16_compressed_instr_c_extension

    # Expected: Access succeeds or traps based on cache line alignment
    la      s0, cache_line_boundary_data
    addi    s0, s0, -4              # Misaligned address crossing cache line
    ld      t0, 0(s0)               # Load double-word crossing cache line
    j       test_16_compressed_instr_c_extension

    # -----------------------------------------
    # Test 16: Compressed Instructions (C Extension)
    # -----------------------------------------
test_16_compressed_instr_c_extension:
    CHECK_TEST_BIT 16, test_17_misaligned_jump_c_extension

    # Expected: If C extension is implemented, misaligned fetch at 16-bit boundary succeeds
    # Otherwise, traps due to instruction address misalignment
    .align 2
    c.add   x5, x6                  # Compressed instruction
    c.j     test_17_misaligned_jump_c_extension  # Jump to next test

    # -----------------------------------------
    # Test 17: Misaligned Jump Target with C Extension
    # -----------------------------------------
test_17_misaligned_jump_c_extension:
    CHECK_TEST_BIT 17, test_18_fences_and_misaligned_accesses

    # Expected: If IALIGN=16, jump to 16-bit aligned address succeeds
    # Otherwise, traps due to instruction address misalignment
    la      s0, misaligned_jump_target
    jr      s0                      # Jump to 16-bit aligned address

    # Execution resumes here after trap handler adjusts mepc
    j       test_18_fences_and_misaligned_accesses

    .balign 2
misaligned_jump_target:
    c.nop                           # Compressed NOP
    c.j     test_18_fences_and_misaligned_accesses

    # -----------------------------------------
    # Test 18: Fences and Misaligned Accesses
    # -----------------------------------------
test_18_fences_and_misaligned_accesses:
    CHECK_TEST_BIT 18, test_19_misaligned_amo_zam_extension

    # Expected: Fences do not affect misaligned access exceptions
    fence                           # Memory fence
    la      s0, misaligned_data_word
    lw      t0, 2(s0)               # Load word from misaligned address
    j       test_19_misaligned_amo_zam_extension

    # -----------------------------------------
    # Test 19: Misaligned AMO with Zam Extension
    # -----------------------------------------
test_19_misaligned_amo_zam_extension:
    CHECK_TEST_BIT 19, test_20_misaligned_vector_whole_reg

    # Expected: If Zam extension is implemented, misaligned AMOs are allowed
    # Otherwise, traps due to misaligned address
    la      s0, misaligned_atomic_addr
    addi    s0, s0, 1               # Adjust s0 to misaligned address
    li      t1, 0xDEADFACE
    amoswap.w.aq t2, t1, (s0)       # Atomic swap on misaligned address
    la      t3, result_misaligned_amo_zam
    sw      t2, 0(t3)               # Store result for checking
    j       test_20_misaligned_vector_whole_reg

    # -----------------------------------------
    # Test 20: Misaligned Access with Vector Whole Register Load/Store
    # -----------------------------------------
test_20_misaligned_vector_whole_reg:
    CHECK_TEST_BIT 20, test_case_end

    # Expected: Trap occurs if misaligned accesses not supported
    la      s0, misaligned_vector_whole_data
    vl1r.v  v0, (s0)                # Load whole register from misaligned address
    la      s1, result_misaligned_vl1r
    vs1r.v  v0, (s1)                # Store whole register for checking

    # -----------------------------------------
    # End of Tests
    # -----------------------------------------
test_case_end:
    csrw    mtvec, s0               # Restore the original mtvec value

    # Restore callee-saved registers
    ld      s7, 0(sp)
    ld      s6, 8(sp)
    ld      s5, 16(sp)
    ld      s4, 24(sp)
    ld      s3, 32(sp)
    ld      s2, 40(sp)
    ld      s1, 48(sp)
    ld      s0, 56(sp)
    addi    sp, sp, 64              # Adjust stack pointer back
    ret                             # Return from function

    .section .text
    .globl reset_registers
    .align 4

reset_registers:
    # Reset Argument Registers (a0 - a7)
    li      a0, 0                   # x10
    li      a1, 0                   # x11
    li      a2, 0                   # x12
    li      a3, 0                   # x13
    li      a4, 0                   # x14
    li      a5, 0                   # x15
    li      a6, 0                   # x16
    li      a7, 0                   # x17

    # Reset Temporary Registers (t0 - t6)
    li      t0, 0                   # x5
    li      t1, 0                   # x6
    li      t2, 0                   # x7
    li      t3, 0                   # x28
    li      t4, 0                   # x29
    li      t5, 0                   # x30
    li      t6, 0                   # x31

    ret                             # Return to caller


    # -----------------------------------------
    # Trap Handler
    # -----------------------------------------
    .section .text.trap
    .align 4
    .globl trap_handler

trap_handler:
    # Save registers
    addi    sp, sp, -32
    sd      ra, 24(sp)
    sd      t0, 16(sp)
    sd      t1, 8(sp)
    sd      t2, 0(sp)

    csrr    t5, mcause              # Read the cause of the trap
    csrr    t6, mepc                # Read the exception program counter
    csrr    t3, mtval               # Read the trap value (faulting address)
    # Set trap_occurred flag
    li      t0, 1
    la      t1, trap_occurred
    sw      t0, 0(t1)

    # Handle specific exceptions
    li      t0, 0                   # Instruction address misaligned
    beq     t5, t0, handle_misaligned_fetch

    li      t0, 2                   # Illegal instruction
    beq     t5, t0, handle_illegal_instruction

    li      t0, 4                   # Load address misaligned
    beq     t5, t0, handle_load_address_misaligned

    li      t0, 6                   # Store address misaligned
    beq     t5, t0, handle_store_address_misaligned

    # Default: Unknown exception, halt
    j       trap_halt


handle_misaligned_fetch:
    # Determine instruction length
    lhu     t0, 0(t6)               # Load halfword from faulting instruction
    andi    t1, t0, 3               # Check bits [1:0] to determine length
    beqz    t1, adjust_32bit        # If bits [1:0] == 0, it's 32-bit
    addi    t6, t6, 2               # 16-bit instruction
    j       adjust_mepc
adjust_32bit:
    addi    t6, t6, 4               # 32-bit instruction
adjust_mepc:
    csrw    mepc, t6                # Update mepc to skip the faulting instruction
    j       trap_return

handle_illegal_instruction:
    # Same logic as handle_misaligned_fetch
    lhu     t0, 0(t6)
    andi    t1, t0, 3
    beqz    t1, adjust_32bit_illegal
    addi    t6, t6, 2
    j       adjust_mepc_illegal
adjust_32bit_illegal:
    addi    t6, t6, 4
adjust_mepc_illegal:
    csrw    mepc, t6
    j       trap_return

handle_misaligned_load:
    addi    t6, t6, 4               # Adjust mepc
    csrw    mepc, t6
    j       trap_return

handle_misaligned_store:
    addi    t6, t6, 4               # Adjust mepc
    csrw    mepc, t6
    j       trap_return

handle_instruction_access_fault:
    addi    t6, t6, 4               # Adjust mepc
    csrw    mepc, t6
    j       trap_return

handle_load_address_misaligned:
    # Load the faulting instruction halfword
    lhu     t0, 0(t6)               # t0 = [mepc]
    andi    t1, t0, 3               # t1 = t0 & 0x3 (bits [1:0])
    li      t2, 3                   # t2 = 3
    bne     t1, t2, adjust_16bit_load
    addi    t6, t6, 4               # 32-bit instruction
    j       adjust_mepc_load
adjust_16bit_load:
    addi    t6, t6, 2               # 16-bit instruction
adjust_mepc_load:
    csrw    mepc, t6                # Update mepc to skip the faulting instruction
    j       trap_return


handle_store_address_misaligned:
    # Determine instruction length as before
    lhu     t0, 0(t6)               # Load halfword from faulting instruction
    andi    t1, t0, 3               # t1 = t0 & 0x3
    li      t2, 3
    bne     t1, t2, adjust_16bit_store
    addi    t6, t6, 4               # 32-bit instruction
    j       adjust_mepc_store
adjust_16bit_store:
    addi    t6, t6, 2               # 16-bit instruction
adjust_mepc_store:
    csrw    mepc, t6                # Update mepc
    j       trap_return


trap_return:
    # Restore registers
    ld      t2, 0(sp)
    ld      t1, 8(sp)
    ld      t0, 16(sp)
    ld      ra, 24(sp)
    addi    sp, sp, 32
    mret                            # Return from trap

trap_halt:
    # Use wfi instruction to halt execution
    wfi

    # -----------------------------------------
    # Data Section
    # -----------------------------------------
    .section .data
    .align 4

    # Aligned data for Test Case 2
aligned_data_byte:
    .byte 0x12

    # Misaligned data for Test Case 3
misaligned_data_byte:
    .byte 0x00, 0x34               # Misaligned byte at offset 1

    # Aligned data for Test Case 4
aligned_data_half:
    .half 0x5678

    # Misaligned data for Test Case 5
misaligned_data_half:
    .byte 0x00, 0x9A, 0xBC         # Misaligned half-word starting at offset 1

    # Aligned data for Test Case 6
aligned_data_word:
    .word 0xDEF01234

    # Misaligned data for Test Case 7
misaligned_data_word:
    .byte 0x00, 0x00, 0x56, 0x78, 0x9A  # Misaligned word starting at offset 2

    # Aligned data for Test Case 8
aligned_data_dword:
    .dword 0x0123456789ABCDEF

    # Misaligned data for Test Case 9
misaligned_data_dword:
    .byte 0x00, 0x00, 0x00, 0x00, 0x12, 0x34, 0x56, 0x78, 0x9A  # Misaligned double-word starting at offset 4

    # Misaligned atomic address for Test Case 10 and 19
misaligned_atomic_addr:
    .byte 0x00, 0x00, 0x00, 0x00, 0x00

    # Misaligned LR/SC address for Test Case 11
misaligned_lrsc_addr:
    .byte 0xAA, 0xBB, 0xCC, 0xDD, 0xEE

    # Misaligned vector data for Test Case 12
misaligned_vector_data:
    .byte 0x11, 0x22, 0x33, 0x44, 0x55

misaligned_vector_data_store:
    .space 32                      # Space for vector store

    # Misaligned floating-point data for Test Case 13
misaligned_fp_data:
    .byte 0x00, 0x00, 0x80, 0x3F, 0x00  # 1.0f in IEEE 754 format with misalignment

    # Page boundary data for Test Case 14
    .align 12                       # Align to 4KB page boundary
page_boundary_data:
    .space 4096                     # Allocate 4KB page

    # Cache line boundary data for Test Case 15
    .align 6                        # Align to 64-byte cache line boundary
cache_line_boundary_data:
    .space 64                       # Allocate 64 bytes

    # Misaligned vector whole data for Test Case 20
misaligned_vector_whole_data:
    .byte 0x00, 0x01, 0x02, 0x03, 0x04

    # Result placeholders for checking in C or for further analysis
    .align 8

    .globl result_misaligned_lh
result_misaligned_lh:
    .space 4                       # Space to store result of misaligned lh

    .globl result_misaligned_lw
result_misaligned_lw:
    .space 4                       # Space to store result of misaligned lw

    .globl result_misaligned_ld
result_misaligned_ld:
    .space 8                       # Space to store result of misaligned ld

    .globl result_misaligned_amo
result_misaligned_amo:
    .space 4                       # Space to store result of misaligned AMO

    .globl result_misaligned_lrsc
result_misaligned_lrsc:
    .space 4                       # Space to store result of misaligned LR/SC

    .globl result_misaligned_vl
result_misaligned_vl:
    .space 32                      # Space to store result of misaligned vector load

    .globl result_misaligned_flw
result_misaligned_flw:
    .space 4                       # Space to store result of misaligned floating-point load

    .globl result_misaligned_amo_zam
result_misaligned_amo_zam:
    .space 4                       # Space to store result of misaligned AMO with Zam extension

    .globl result_misaligned_vl1r
result_misaligned_vl1r:
    .space 64                      # Space to store result of misaligned whole vector load

    # End of assembly test file
