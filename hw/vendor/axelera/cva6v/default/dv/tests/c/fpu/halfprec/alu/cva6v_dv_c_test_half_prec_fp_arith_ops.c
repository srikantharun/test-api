// This is a test file for half_prec_fp_arith_ops
// CVA6V directed C tests : Author : Abhilash Chadhar
// In the provided test file, the following half-precision floating-point operations are explicitly tested:
// fadd.h - Half-precision floating-point addition (1.0 + 1000.0 = 1001.0).
// fsub.h - Half-precision floating-point subtraction (1000.0 - 1.5 = 998.5).
// fmul.h - Half-precision floating-point multiplication (1.5 * 1000.0 = 1500.0).
// fdiv.h - Half-precision floating-point division (1000.0 / -1.0 = -1000.0).
// fsqrt.h - Half-precision floating-point square root (sqrt(1.5) = ~1.224745).
// fsgnj.h - Half-precision floating-point sign injection (sign from -1.5, value from 1.0).
// fsgnjn.h - Half-precision floating-point sign negation (negate sign from -1.5, value from 1.0).
// fsgnjx.h - Half-precision floating-point sign XOR (XOR sign from -1.5, value from 1.0).
// fmin.h - Half-precision floating-point minimum (min of 1000.0 and -1000.0 -> -1000.0).
// fmax.h - Half-precision floating-point maximum (max of 1000.0 and -1000.0 -> 1000.0).

#include "common.h"

// Declare the half-precision floating-point values array
uint16_t half_float_values[15];
uint16_t expected_half_values[15]; // Store expected values for comparisons

// Function to initialize half-precision floating-point values and expected results
void initialize_half_float_values() {
    half_float_values[0] = 0x0000;  // Zero
    half_float_values[1] = 0x8000;  // Negative Zero
    half_float_values[2] = 0x3C00;  // 1.0
    half_float_values[3] = 0xBC00;  // -1.0
    half_float_values[4] = 0x3E00;  // 1.5
    half_float_values[5] = 0xBE00;  // -1.5
    half_float_values[6] = 0x63D0;  // 1000.0
    half_float_values[7] = 0xE3D0;  // -1000.0
    half_float_values[8] = 0x0400;  // Small positive denormalized
    half_float_values[9] = 0x8400;  // Small negative denormalized
    half_float_values[10] = 0x7BFF; // Very large positive (max normal)
    half_float_values[11] = 0xFBFF; // Very large negative (min normal)

    // Special values
    half_float_values[12] = 0x7C00; // Positive Infinity
    half_float_values[13] = 0xFC00; // Negative Infinity
    half_float_values[14] = 0x7E00; // NaN

    // Corrected expected results for operations
    expected_half_values[0] = 0x63D2;  // 1.0 + 1000.0 = 1001.0
    expected_half_values[1] = 0x63CD;  // 1000.0 - 1.5 = 998.5
    expected_half_values[2] = 0x65DC;  // 1.5 * 1000.0 = 1500.0
    expected_half_values[3] = 0xE3D0;  // 1000.0 / -1.0 = -1000.0
    expected_half_values[4] = 0x3CE6;  // sqrt(1.5) = ~1.224745
    expected_half_values[5] = 0xBC00;  // sign from -1.5, value from 1.0 = -1.0
    expected_half_values[6] = 0x3C00;  // negate sign from -1.5, value from 1.0 = 1.0
    expected_half_values[7] = 0xBC00;  // XOR sign from -1.5, value from 1.0 = -1.0
    expected_half_values[8] = 0xE3D0;  // min of 1000.0 and -1000.0 = -1000.0
    expected_half_values[9] = 0x63D0;  // max of 1000.0 and -1000.0 = 1000.0
}

// Macro to check the value of a half-precision floating-point register and print the result
#define CHECK_FREG_H(op, dest, expected_idx, scenario)                            \
    do {                                                                          \
        uint16_t dest_val;                                                        \
        asm volatile ("fsh " #dest ", %0" : "=m"(dest_val));                      \
        float actual_float = half_to_float(dest_val);                             \
        float expected_float = half_to_float(expected_half_values[expected_idx]);  \
        const char *result = (fabsf(actual_float - expected_float) <= HALF_FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        printf("%-50s | actual=0x%04x | expected=0x%04x | result=%s\n", scenario, dest_val, expected_half_values[expected_idx], result); \
        if (strcmp(result, "FAIL") == 0) pass = 0;                                \
    } while(0)

// Macro to perform a half-precision floating-point operation and check the result
#define TEST_HFOP(dest, src1, src2, op, src1_idx, src2_idx, expected_idx, scenario) \
    do {                                                                            \
        asm volatile ("flh " #src1 ", %0" :: "m"(half_float_values[src1_idx]));      \
        asm volatile ("flh " #src2 ", %0" :: "m"(half_float_values[src2_idx]));      \
        asm volatile (#op " " #dest ", " #src1 ", " #src2);                         \
        CHECK_FREG_H(#op, dest, expected_idx, scenario);                            \
    } while(0)

// Macro to perform the fsqrt.h operation and check the result (only one source operand)
#define TEST_HFSQRT_OP(dest, src1, op, src1_idx, expected_idx, scenario)            \
    do {                                                                            \
        asm volatile ("flh " #src1 ", %0" :: "m"(half_float_values[src1_idx]));      \
        asm volatile (#op " " #dest ", " #src1);                                    \
        CHECK_FREG_H(#op, dest, expected_idx, scenario);                            \
    } while(0)

int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the half-precision floating-point values
    initialize_half_float_values();

    // Print table header
    printf("%-50s | %-12s | %-12s | %s\n", "Scenario", "Actual", "Expected", "Result");
    printf("--------------------------------------------------------------------------------------\n");

    // Test scenarios
    TEST_HFOP(fa0, fa1, fa2, fadd.h, 2, 6, 0, "fadd.h (1.0 + 1000.0 = 1001.0)");
    TEST_HFOP(fa0, fa1, fa2, fsub.h, 6, 4, 1, "fsub.h (1000.0 - 1.5 = 998.5)");
    TEST_HFOP(fa0, fa1, fa2, fmul.h, 4, 6, 2, "fmul.h (1.5 * 1000.0 = 1500.0)");
    TEST_HFOP(fa0, fa1, fa2, fdiv.h, 6, 3, 3, "fdiv.h (1000.0 / -1.0 = -1000.0)");
    TEST_HFSQRT_OP(fa0, fa1, fsqrt.h, 4, 4, "fsqrt.h (sqrt(1.5) = 1.224745)");
    TEST_HFOP(fa0, fa1, fa2, fsgnj.h, 2, 5, 5, "fsgnj.h (sign from -1.5, value from 1.0)");
    TEST_HFOP(fa0, fa1, fa2, fsgnjn.h, 2, 5, 6, "fsgnjn.h (negate sign from -1.5, value from 1.0)");
    TEST_HFOP(fa0, fa1, fa2, fsgnjx.h, 2, 5, 7, "fsgnjx.h (XOR sign from -1.5, value from 1.0)");
    TEST_HFOP(fa0, fa1, fa2, fmin.h, 6, 7, 8, "fmin.h (min of 1000.0 and -1000.0 -> -1000.0)");
    TEST_HFOP(fa0, fa1, fa2, fmax.h, 6, 7, 9, "fmax.h (max of 1000.0 and -1000.0 -> 1000.0)");

    if (pass) {
        printf("All half-precision tests passed.\n");
    } else {
        printf("Some half-precision tests failed.\n");
    }

    return 0;
}
