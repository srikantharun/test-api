// This is a test file for single_prec_fp_arith_ops
// CVA6V directed C tests : Author : Abhilash Chadhar
// In the provided test file, the following floating-point operations are explicitly tested:
// fadd.s - Floating-point addition (1.0 + 1000.0 = 1001.0).
// fsub.s - Floating-point subtraction (1000.0 - 1.5 = 998.5).
// fmul.s - Floating-point multiplication (1.5 * 1000.0 = 1500.0).
// fdiv.s - Floating-point division (1000.0 / -1.0 = -1000.0).
// fsqrt.s - Floating-point square root (sqrt(1.5) = 1.224745).
// fsgnj.s - Floating-point sign injection (sign from -1.5, value from 1.0).
// fsgnjn.s - Floating-point sign negation (negate sign from -1.5, value from 1.0).
// fsgnjx.s - Floating-point sign XOR (XOR sign from -1.5, value from 1.0).
// fmin.s - Floating-point minimum (min of 1000.0 and -1000.0 -> -1000.0).
// fmax.s - Floating-point maximum (max of 1000.0 and -1000.0 -> 1000.0).

#include "common.h"

// Declare the floating-point values array
float float_values[15];
float expected_values[15]; // Store expected values for comparisons

// Function to initialize floating-point values and expected results
void initialize_float_values() {
    float_values[0] = 0.0f;                // 0x00000000 Zero
    float_values[1] = -0.0f;               // 0x80000000 Negative Zero
    float_values[2] = 1.0f;                // 0x3F800000 Normal positive
    float_values[3] = -1.0f;               // 0xBF800000 Normal negative
    float_values[4] = 1.5f;                // 0x3FC00000 Positive fractional
    float_values[5] = -1.5f;               // 0xBFC00000 Negative fractional
    float_values[6] = 1000.0f;             // 0x447A0000 Large positive
    float_values[7] = -1000.0f;            // 0xC47A0000 Large negative
    float_values[8] = 1e-10f;              // 0x2E934791 Small positive
    float_values[9] = -1e-10f;             // 0xAE934791 Small negative
    float_values[10] = 1e10f;              // 0x501502F9 Very large positive
    float_values[11] = -1e10f;             // 0xD01502F9 Very large negative

    // Special values: Infinity, Negative Infinity, NaN
    memcpy(&float_values[12], &(float){0x7F800000}, sizeof(float)); // Positive Infinity
    memcpy(&float_values[13], &(float){0xFF800000}, sizeof(float)); // Negative Infinity
    memcpy(&float_values[14], &(float){0x7FC00000}, sizeof(float)); // NaN

    // Set up expected values for each operation (aligned with test order)
    expected_values[0] = 1001.0f;  // 1.0 + 1000.0
    expected_values[1] = 998.5f;   // 1000.0 - 1.5
    expected_values[2] = 1500.0f;  // 1.5 * 1000.0
    expected_values[3] = -1000.0f; // 1000.0 / -1.0
    expected_values[4] = 1.224745f; // sqrt(1.5)
    expected_values[5] = -1.0f;    // sign from -1.5, value from 1.0
    expected_values[6] = 1.0f;     // negate sign from -1.5, value from 1.0
    expected_values[7] = -1.0f;    // XOR sign from -1.5, value from 1.0
    expected_values[8] = -1000.0f; // min of 1000.0 and -1000.0
    expected_values[9] = 1000.0f;  // max of 1000.0 and -1000.0
}

// Macro to check the value of a floating-point register and print the result
// Macro to check the value of a floating-point register and print the result
#define CHECK_FREG(op, dest, src1, src2, expected_idx, scenario)               \
    do {                                                                       \
        float dest_val, src1_val, src2_val;                                    \
        char dest_str[50], src1_str[50], src2_str[50], expected_str[50];       \
        asm volatile ("fsw " #dest ", %0" : "=m"(dest_val));                   \
        asm volatile ("fsw " #src1 ", %0" : "=m"(src1_val));                   \
        asm volatile ("fsw " #src2 ", %0" : "=m"(src2_val));                   \
        float_to_str(dest_val, dest_str, 6);                                   \
        float_to_str(src1_val, src1_str, 6);                                   \
        float_to_str(src2_val, src2_str, 6);                                   \
        float_to_str(expected_values[expected_idx], expected_str, 6);          \
        const char *result = (fabsf(dest_val - expected_values[expected_idx]) <= FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        CHECK_TRUE(fabsf(dest_val - expected_values[expected_idx]) <= FLOAT_TOLERANCE, \
            "[CHECK FAILED] %s: Expected \'%s\', Was \'%s\'", scenario, expected_str, dest_str); \
    } while(0)


// Macro to perform a floating-point operation and check the result
#define TEST_FOP(dest, src1, src2, op, src1_idx, src2_idx, expected_idx, scenario) \
    do {                                                                           \
        asm volatile ("flw " #src1 ", %0" :: "m"(float_values[src1_idx]));         \
        asm volatile ("flw " #src2 ", %0" :: "m"(float_values[src2_idx]));         \
        asm volatile (#op " " #dest ", " #src1 ", " #src2);                        \
        CHECK_FREG(#op, dest, src1, src2, expected_idx, scenario);                 \
    } while(0)

// Macro to perform the fsqrt.s operation and check the result (only one source operand)
#define TEST_FSQRT_OP(dest, src1, op, src1_idx, expected_idx, scenario)            \
    do {                                                                           \
        asm volatile ("flw " #src1 ", %0" :: "m"(float_values[src1_idx]));         \
        asm volatile (#op " " #dest ", " #src1);                                   \
        CHECK_FREG(#op, dest, src1, src1, expected_idx, scenario);                 \
    } while(0)


// Expanded Mega Macro to test more combinations of registers for each operation
#define TEST_ALL_COMBINATIONS(op, src1_idx, src2_idx, expected_idx)            \
    do {                                                                       \
        TEST_FOP(fa0, fa1, fa2, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa1, fa2, fa3, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa2, fa3, fa4, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa3, fa4, fa5, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa4, fa5, fa6, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa5, fa6, fa7, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa6, fa7, fa0, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa7, fa0, fa1, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa0, fa2, fa4, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa1, fa3, fa5, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa2, fa4, fa6, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa3, fa5, fa7, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa4, fa6, fa0, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa5, fa7, fa1, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa6, fa0, fa2, op, src1_idx, src2_idx, expected_idx);         \
        TEST_FOP(fa7, fa1, fa3, op, src1_idx, src2_idx, expected_idx);         \
    } while(0)

// Expanded Mega Macro to test more combinations of registers for fsqrt.s
#define TEST_ALL_SQRT_COMBINATIONS(op, src1_idx, expected_idx)                 \
    do {                                                                       \
        TEST_FSQRT_OP(fa0, fa1, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa1, fa2, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa2, fa3, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa3, fa4, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa4, fa5, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa5, fa6, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa6, fa7, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa7, fa0, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa0, fa2, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa1, fa3, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa2, fa4, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa3, fa5, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa4, fa6, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa5, fa7, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa6, fa0, op, src1_idx, expected_idx);                   \
        TEST_FSQRT_OP(fa7, fa1, op, src1_idx, expected_idx);                   \
    } while(0)

int main() {
    testcase_init(); // Initialize test case counters

    // Initialize the special floating-point values
    initialize_float_values();

    // Print table header
    PRINT_HEADER();

    // Test scenarios using testutils
    TEST_FOP(fa0, fa1, fa2, fadd.s, 2, 6, 0, "fadd.s (1.0f + 1000.0f = 1001.0f)");
    TEST_FOP(fa0, fa1, fa2, fsub.s, 6, 4, 1, "fsub.s (1000.0f - 1.5f = 998.5f)");
    TEST_FOP(fa0, fa1, fa2, fmul.s, 4, 6, 2, "fmul.s (1.5f * 1000.0f = 1500.0f)");
    TEST_FOP(fa0, fa1, fa2, fdiv.s, 6, 3, 3, "fdiv.s (1000.0f / -1.0f = -1000.0f)");
    TEST_FSQRT_OP(fa0, fa1, fsqrt.s, 4, 4, "fsqrt.s (sqrt(1.5f) = 1.224745f)");
    TEST_FOP(fa0, fa1, fa2, fsgnj.s, 2, 5, 5, "fsgnj.s (sign from -1.5, value from 1.0)");
    TEST_FOP(fa0, fa1, fa2, fsgnjn.s, 2, 5, 6, "fsgnjn.s (negate sign from -1.5, value from 1.0)");
    TEST_FOP(fa0, fa1, fa2, fsgnjx.s, 2, 5, 7, "fsgnjx.s (XOR sign from -1.5, value from 1.0)");
    TEST_FOP(fa0, fa1, fa2, fmin.s, 6, 7, 8, "fmin.s (min of 1000.0 and -1000.0 -> -1000.0)");
    TEST_FOP(fa0, fa1, fa2, fmax.s, 6, 7, 9, "fmax.s (max of 1000.0 and -1000.0 -> 1000.0)");

    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }

    return 0;
}

