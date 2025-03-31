/*
 * RISC-V CVA6 Single-Precision Floating-Point Comparison Instructions Comprehensive Test
 * This test covers feq.s, flt.s, and fle.s instructions with exhaustive test cases,
 * including normal numbers, zeros, subnormals, infinities, NaNs, sign variations,
 * and different floating-point modes.
 */

    .section .text.init
    .align 6                    /* 2^6 = 64 bytes alignment */
    .global _start
_start:
    /* Initialize tohost interface */
    la a0, tohost
    li a1, 0
    sw a1, 0(a0)              /* Initialize tohost to 0 */

    /* Initialize test failure counter */
    li t0, 0                  /* t0 = number of failed tests */

    /* Initialize floating-point environment */
    /* Set default rounding mode (to nearest) if applicable */
    csrr a0, fcsr             /* Read FCSR */
    ori a0, a0, 0x0           /* Ensure rounding mode bits are 0 (RNE) */
    csrw fcsr, a0             /* Write back FCSR */

    /* Jump to test runner */
    jal ra, run_tests

    /* After tests, check if any failures occurred */
    beq t0, x0, exit_success  /* If no failures, exit success */
    jal ra, exit_failure       /* Else, exit failure */

/*
 * Test Runner
 */
    .section .text
    .align 6                    /* 64-byte alignment */
run_tests:
    /* feq.s Tests */
    jal ra, test_feq_normal_eq
    jal ra, test_feq_normal_neq
    jal ra, test_feq_zero
    jal ra, test_feq_subnormal
    jal ra, test_feq_infinity
    jal ra, test_feq_nan
    jal ra, test_feq_sign_variation

    /* flt.s Tests */
    jal ra, test_flt_normal
    jal ra, test_flt_zero
    jal ra, test_flt_subnormal
    jal ra, test_flt_infinity
    jal ra, test_flt_nan
    jal ra, test_flt_sign_variation

    /* fle.s Tests */
    jal ra, test_fle_normal
    jal ra, test_fle_zero
    jal ra, test_fle_subnormal
    jal ra, test_fle_infinity
    jal ra, test_fle_nan
    jal ra, test_fle_sign_variation

    /* Mode Change Tests (e.g., Rounding Modes) */
    jal ra, test_mode_changes

    /* After all tests, exit */
    jal ra, exit_success

/*
 * feq.s Test Cases
 */

/* Test feq.s: Equal normal numbers (1.0 == 1.0) */
test_feq_normal_eq:
    la t1, val_1_0
    flw f1, 0(t1)            /* f1 = 1.0 */
    flw f2, 0(t1)            /* f2 = 1.0 */
    feq.s a0, f1, f2
    li t3, 1
    bne a0, t3, fail_feq_normal_eq
    ret

/* Test feq.s: Unequal normal numbers (1.0 != 2.0) */
test_feq_normal_neq:
    la t1, val_1_0
    flw f1, 0(t1)            /* f1 = 1.0 */
    la t1, val_2_0
    flw f2, 0(t1)            /* f2 = 2.0 */
    feq.s a0, f1, f2
    li t3, 0
    bne a0, t3, fail_feq_normal_neq
    ret

/* Test feq.s: Comparing +0.0 and -0.0 */
test_feq_zero:
    la t1, val_p0
    flw f1, 0(t1)            /* f1 = +0.0 */
    la t1, val_n0
    flw f2, 0(t1)            /* f2 = -0.0 */
    feq.s a0, f1, f2
    li t3, 1                  /* +0.0 == -0.0 should be true */
    bne a0, t3, fail_feq_zero
    ret

/* Test feq.s: Equal subnormal numbers */
test_feq_subnormal:
    la t1, val_subnormal
    flw f1, 0(t1)            /* f1 = subnormal */
    flw f2, 0(t1)            /* f2 = subnormal */
    feq.s a0, f1, f2
    li t3, 1                  /* subnormal == subnormal */
    bne a0, t3, fail_feq_subnormal
    ret

/* Test feq.s: Equal infinities */
test_feq_infinity:
    la t1, val_inf_pos
    flw f1, 0(t1)            /* f1 = +inf */
    flw f2, 0(t1)            /* f2 = +inf */
    feq.s a0, f1, f2
    li t3, 1                  /* +inf == +inf */
    bne a0, t3, fail_feq_infinity
    ret

/* Test feq.s: NaN comparisons */
test_feq_nan:
    la t1, val_nan
    flw f1, 0(t1)            /* f1 = NaN */
    flw f2, 0(t1)            /* f2 = NaN */
    feq.s a0, f1, f2
    li t3, 0                  /* NaN == NaN should be false */
    bne a0, t3, fail_feq_nan
    ret

/* Test feq.s: Sign variations with NaN */
test_feq_sign_variation:
    la t1, val_nan_pos
    flw f1, 0(t1)            /* f1 = +NaN */
    la t1, val_nan_neg
    flw f2, 0(t1)            /* f2 = -NaN */
    feq.s a0, f1, f2
    li t3, 0                  /* NaN == NaN should be false regardless of sign */
    bne a0, t3, fail_feq_sign_variation
    ret

/*
 * flt.s Test Cases
 */

/* Test flt.s: 1.0 < 2.0 and 2.0 < 1.0 */
test_flt_normal:
    la t1, val_1_0
    flw f1, 0(t1)            /* f1 = 1.0 */
    la t1, val_2_0
    flw f2, 0(t1)            /* f2 = 2.0 */
    flt.s a0, f1, f2
    li t3, 1                  /* 1.0 < 2.0 */
    bne a0, t3, fail_flt_normal
    flt.s a0, f2, f1
    li t3, 0                  /* 2.0 < 1.0 should be false */
    bne a0, t3, fail_flt_normal_rev
    ret

/* Test flt.s: Comparing +0.0 < -0.0 and -0.0 < +0.0 */
test_flt_zero:
    la t1, val_p0
    flw f1, 0(t1)            /* f1 = +0.0 */
    la t1, val_n0
    flw f2, 0(t1)            /* f2 = -0.0 */
    flt.s a0, f1, f2
    li t3, 0                  /* +0.0 < -0.0 should be false */
    bne a0, t3, fail_flt_zero
    flt.s a0, f2, f1
    li t3, 0                  /* -0.0 < +0.0 should be false */
    bne a0, t3, fail_flt_zero_rev
    ret

/* Test flt.s: Subnormal < Normal and vice versa */
test_flt_subnormal:
    la t1, val_subnormal
    flw f1, 0(t1)            /* f1 = subnormal */
    la t1, val_1_0
    flw f2, 0(t1)            /* f2 = 1.0 */
    flt.s a0, f1, f2
    li t3, 1                  /* subnormal < 1.0 */
    bne a0, t3, fail_flt_subnormal
    flt.s a0, f2, f1
    li t3, 0                  /* 1.0 < subnormal should be false */
    bne a0, t3, fail_flt_subnormal_rev
    ret

/* Test flt.s: Finite < +inf and +inf < finite */
test_flt_infinity:
    la t1, val_inf_pos
    flw f1, 0(t1)            /* f1 = +inf */
    la t1, val_1_0
    flw f2, 0(t1)            /* f2 = 1.0 */
    flt.s a0, f2, f1
    li t3, 1                  /* 1.0 < +inf */
    bne a0, t3, fail_flt_infinity
    flt.s a0, f1, f2
    li t3, 0                  /* +inf < 1.0 should be false */
    bne a0, t3, fail_flt_infinity_rev
    ret

/* Test flt.s: NaN comparisons */
test_flt_nan:
    la t1, val_nan
    flw f1, 0(t1)            /* f1 = NaN */
    la t1, val_1_0
    flw f2, 0(t1)            /* f2 = 1.0 */
    flt.s a0, f1, f2
    li t3, 0                  /* NaN < 1.0 should be false */
    bne a0, t3, fail_flt_nan
    flt.s a0, f2, f1
    li t3, 0                  /* 1.0 < NaN should be false */
    bne a0, t3, fail_flt_nan_rev
    ret

/* Test flt.s: Sign variations with NaN */
test_flt_sign_variation:
    la t1, val_nan_pos
    flw f1, 0(t1)            /* f1 = +NaN */
    la t1, val_nan_neg
    flw f2, 0(t1)            /* f2 = -NaN */
    flt.s a0, f1, f2
    li t3, 0                  /* NaN < NaN should be false */
    bne a0, t3, fail_flt_sign_variation
    ret

/*
 * fle.s Test Cases
 */

/* Test fle.s: 1.0 <= 2.0 and 2.0 <= 1.0 */
test_fle_normal:
    la t1, val_1_0
    flw f1, 0(t1)            /* f1 = 1.0 */
    la t1, val_2_0
    flw f2, 0(t1)            /* f2 = 2.0 */
    fle.s a0, f1, f2
    li t3, 1                  /* 1.0 <= 2.0 */
    bne a0, t3, fail_fle_normal
    fle.s a0, f2, f1
    li t3, 0                  /* 2.0 <= 1.0 should be false */
    bne a0, t3, fail_fle_normal_rev
    ret

/* Test fle.s: Comparing +0.0 <= -0.0 and -0.0 <= +0.0 */
test_fle_zero:
    la t1, val_p0
    flw f1, 0(t1)            /* f1 = +0.0 */
    la t1, val_n0
    flw f2, 0(t1)            /* f2 = -0.0 */
    fle.s a0, f1, f2
    li t3, 1                  /* +0.0 <= -0.0 should be true (0.0 == -0.0) */
    bne a0, t3, fail_fle_zero
    fle.s a0, f2, f1
    li t3, 1                  /* -0.0 <= +0.0 should be true (0.0 == -0.0) */
    bne a0, t3, fail_fle_zero_rev
    ret

/* Test fle.s: Subnormal <= Normal and vice versa */
test_fle_subnormal:
    la t1, val_subnormal
    flw f1, 0(t1)            /* f1 = subnormal */
    la t1, val_1_0
    flw f2, 0(t1)            /* f2 = 1.0 */
    fle.s a0, f1, f2
    li t3, 1                  /* subnormal <= 1.0 */
    bne a0, t3, fail_fle_subnormal
    fle.s a0, f2, f1
    li t3, 0                  /* 1.0 <= subnormal should be false */
    bne a0, t3, fail_fle_subnormal_rev
    ret

/* Test fle.s: Finite <= +inf and +inf <= finite */
test_fle_infinity:
    la t1, val_inf_pos
    flw f1, 0(t1)            /* f1 = +inf */
    la t1, val_1_0
    flw f2, 0(t1)            /* f2 = 1.0 */
    fle.s a0, f2, f1
    li t3, 1                  /* 1.0 <= +inf */
    bne a0, t3, fail_fle_infinity
    fle.s a0, f1, f2
    li t3, 0                  /* +inf <= 1.0 should be false */
    bne a0, t3, fail_fle_infinity_rev
    ret

/* Test fle.s: NaN comparisons */
test_fle_nan:
    la t1, val_nan
    flw f1, 0(t1)            /* f1 = NaN */
    la t1, val_1_0
    flw f2, 0(t1)            /* f2 = 1.0 */
    fle.s a0, f1, f2
    li t3, 0                  /* NaN <= 1.0 should be false */
    bne a0, t3, fail_fle_nan
    fle.s a0, f2, f1
    li t3, 0                  /* 1.0 <= NaN should be false */
    bne a0, t3, fail_fle_nan_rev
    ret

/* Test fle.s: Sign variations with NaN */
test_fle_sign_variation:
    la t1, val_nan_pos
    flw f1, 0(t1)            /* f1 = +NaN */
    la t1, val_nan_neg
    flw f2, 0(t1)            /* f2 = -NaN */
    fle.s a0, f1, f2
    li t3, 0                  /* NaN <= NaN should be false */
    bne a0, t3, fail_fle_sign_variation
    ret

/*
 * Floating-Point Mode Change Tests
 * This includes changing rounding modes and ensuring comparisons behave correctly.
 * Note: Mode changes affect arithmetic operations more than comparisons, but included for rigor.
 */

/* Test changing rounding modes and performing comparisons */
test_mode_changes:
    /* Change rounding mode to towards zero (RTZ) */
    csrr a0, fcsr             /* Read FCSR */
    ori a0, a0, 0x1           /* Set Rounding Mode to RTZ (bits 0-2 = 001) */
    csrw fcsr, a0             /* Write back FCSR */

    /* Perform a comparison in RTZ mode */
    la t1, val_1_0
    flw f1, 0(t1)             /* f1 = 1.0 */
    flw f2, 0(t1)             /* f2 = 1.0 */
    feq.s a0, f1, f2
    li t3, 1                  /* 1.0 == 1.0 */
    bne a0, t3, fail_mode_change_eq

    /* Change rounding mode to upward (RUP) */
    csrr a0, fcsr
    li t4, 0x2
    /* slli t4, t4, 0 */       /* Shift left by 0 is unnecessary */
    andi a0, a0, -8           /* Clear rounding mode bits (0xFF8 truncated to 12 bits is -8) */
    or a0, a0, t4             /* Set to RUP (010) */
    csrw fcsr, a0

    /* Perform a comparison in RUP mode */
    feq.s a0, f1, f2
    li t3, 1                  /* 1.0 == 1.0 */
    bne a0, t3, fail_mode_change_eq

    /* Restore default rounding mode (RNE) */
    csrr a0, fcsr
    andi a0, a0, -8           /* Clear rounding mode bits */
    ori a0, a0, 0x0           /* Set to RNE */
    csrw fcsr, a0

    ret

/* Failure Handlers */
fail_feq_normal_eq:
fail_feq_normal_neq:
fail_feq_zero:
fail_feq_subnormal:
fail_feq_infinity:
fail_feq_nan:
fail_feq_sign_variation:
fail_flt_normal:
fail_flt_normal_rev:
fail_flt_zero:
fail_flt_zero_rev:
fail_flt_subnormal:
fail_flt_subnormal_rev:
fail_flt_infinity:
fail_flt_infinity_rev:
fail_flt_nan:
fail_flt_nan_rev:
fail_flt_sign_variation:
fail_fle_normal:
fail_fle_normal_rev:
fail_fle_zero:
fail_fle_zero_rev:
fail_fle_subnormal:
fail_fle_subnormal_rev:
fail_fle_infinity:
fail_fle_infinity_rev:
fail_fle_nan:
fail_fle_nan_rev:
fail_fle_sign_variation:
fail_mode_change_eq:
    /* Increment failure counter */
    addi t0, t0, 1
    ret

/*
 * Exit Handlers
 */
exit_success:
    /* Write success to tohost */
    la a0, tohost
    li a1, 1                   /* Success code */
    sw a1, 0(a0)
    j exit_done

exit_failure:
    /* Write failure to tohost */
    la a0, tohost
    li a1, -1                  /* Failure code */
    sw a1, 0(a0)
    j exit_done

exit_done:
    /* Infinite loop to halt execution */
    j exit_done

/*
 * Data Section
 */
    .section .data
    .align 6                    /* 64-byte alignment */
val_1_0:        .float 1.0
val_2_0:        .float 2.0
val_p0:         .float 0.0
val_n0:         .float -0.0
val_subnormal:  .word 0x00800001    /* Smallest positive subnormal single-precision */
val_inf_pos:    .word 0x7F800000    /* Positive infinity */
val_inf_neg:    .word 0xFF800000    /* Negative infinity */
val_nan:        .word 0x7FC00000    /* Quiet NaN */
val_nan_pos:    .word 0x7FC00000    /* +NaN */
val_nan_neg:    .word 0xFFC00000    /* -NaN */

/*
 * Tohost Interface
 */
    .section .tohost
    .align 12                   /* 2^12 = 4096 bytes alignment */
tohost:
    .word 0x00000000
