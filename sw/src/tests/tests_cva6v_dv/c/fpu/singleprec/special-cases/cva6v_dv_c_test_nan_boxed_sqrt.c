// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, NaN-boxed single-precision floating-point square root operations are explicitly tested.

#include "common.h"

// Define arrays to store the test values for NaN-boxed inputs and expected results
__attribute__((aligned(4))) float test_values[13]; // Extended for additional test case
__attribute__((aligned(4))) float expected_results[13]; // Extended for additional test case

// Define NaN-boxed representations for various cases
#define NAN_BOXED_ZERO       0x7FC00000U  // NaN-boxed zero (single-precision)
#define NAN_BOXED_INF        0x7F800000U  // NaN-boxed positive infinity (single-precision)
#define NAN_BOXED_NEG_INF    0xFF800000U  // NaN-boxed negative infinity (single-precision)
#define NAN_BOXED_NEG        0xFFC00001U  // NaN-boxed negative number (single-precision)
#define NAN_BOXED_POS        0x7FC00001U  // NaN-boxed positive number (single-precision)
#define NAN_BOXED_NAN        0x7FC00000U  // NaN-boxed NaN (single-precision)
#define NAN_BOXED_SQRT_ZERO  0x7FC00000U  // Specific NaN-boxed zero for issue coverage

// Function to initialize values for testing NaN-boxed square root operations
void initialize_nan_boxed_sqrt_values() {
    // Directly assign values to ensure correct bit patterns
    test_values[0] = *((float*)&(uint32_t){NAN_BOXED_ZERO});       // NaN-boxed zero
    test_values[1] = *((float*)&(uint32_t){NAN_BOXED_INF});        // NaN-boxed positive infinity
    test_values[2] = *((float*)&(uint32_t){NAN_BOXED_NEG_INF});    // NaN-boxed negative infinity
    test_values[3] = *((float*)&(uint32_t){NAN_BOXED_NEG});        // NaN-boxed negative number
    test_values[4] = *((float*)&(uint32_t){NAN_BOXED_POS});        // NaN-boxed positive number
    test_values[5] = *((float*)&(uint32_t){NAN_BOXED_NAN});        // NaN-boxed NaN
    test_values[6] = 4.0f;                                         // Normal positive number
    test_values[7] = -9.0f;                                        // Normal negative number
    test_values[8] = 0.0f;                                         // Normal zero
    test_values[9] = *((float*)&(uint32_t){POS_INFINITY});         // Normal positive infinity
    test_values[10] = *((float*)&(uint32_t){NEG_INFINITY});        // Normal negative infinity
    test_values[11] = *((float*)&(uint32_t){NAN_VALUE});           // Normal NaN
    test_values[12] = *((float*)&(uint32_t){NAN_BOXED_SQRT_ZERO}); // Specific NaN-boxed zero for issue coverage

    // Corrected expected results for sqrt operations
    expected_results[0] = *((float*)&(uint32_t){NAN_VALUE});       // sqrt(NaN-boxed zero) = NaN
    expected_results[1] = *((float*)&(uint32_t){POS_INFINITY});    // sqrt(NaN-boxed positive infinity) = positive infinity
    expected_results[2] = *((float*)&(uint32_t){NAN_VALUE});       // sqrt(NaN-boxed negative infinity) = NaN
    expected_results[3] = *((float*)&(uint32_t){NAN_VALUE});       // sqrt(NaN-boxed negative number) = NaN
    expected_results[4] = *((float*)&(uint32_t){NAN_VALUE});       // sqrt(NaN-boxed positive number) = NaN
    expected_results[5] = *((float*)&(uint32_t){NAN_VALUE});       // sqrt(NaN-boxed NaN) = NaN
    expected_results[6] = 2.0f;                                    // sqrt(4.0f) = 2.0
    expected_results[7] = *((float*)&(uint32_t){NAN_VALUE});       // sqrt(-9.0f) = NaN
    expected_results[8] = 0.0f;                                    // sqrt(0.0f) = 0.0
    expected_results[9] = *((float*)&(uint32_t){POS_INFINITY});    // sqrt(INFINITY) = INFINITY
    expected_results[10] = *((float*)&(uint32_t){NAN_VALUE});      // sqrt(-INFINITY) = NaN
    expected_results[11] = *((float*)&(uint32_t){NAN_VALUE});      // sqrt(NAN) = NaN
    expected_results[12] = *((float*)&(uint32_t){NAN_VALUE});      // sqrt(NaN-boxed zero in issue case) = NaN
}

// Macro to check the result of the square root operation
#define CHECK_SQRT_OP(op, dest, src, expected_idx, scenario)                    \
    do {                                                                        \
        float dest_val;                                                         \
        asm volatile ("fmv.s %0, " #dest : "=f"(dest_val));                     \
        char dest_str[50], expected_str[50];                                    \
        float_to_str(dest_val, dest_str, 6);                                    \
        float_to_str(expected_results[expected_idx], expected_str, 6);          \
        const char *result;                                                     \
        if (isnan(expected_results[expected_idx])) {                            \
            result = isnan(dest_val) ? "PASS" : "FAIL";                         \
        } else if (isinf(expected_results[expected_idx])) {                     \
            result = isinf(dest_val) && (signbit(dest_val) == signbit(expected_results[expected_idx])) ? "PASS" : "FAIL"; \
        } else {                                                                \
            result = (fabsf(dest_val - expected_results[expected_idx]) <= FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        }                                                                       \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                 \
        if (strcmp(result, "FAIL") == 0) pass = 0;                              \
    } while(0)

// Macro to perform the fsqrt.s operation and check the result (only one source operand)
#define TEST_FSQRT_OP(dest, src, op, src_idx, expected_idx, scenario)           \
    do {                                                                        \
        asm volatile ("flw " #src ", %0" :: "m"(test_values[src_idx]));         \
        asm volatile (#op " " #dest ", " #src);                                 \
        CHECK_SQRT_OP(#op, dest, src, expected_idx, scenario);                  \
    } while(0)

int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the NaN-boxed sqrt values and expected results
    initialize_nan_boxed_sqrt_values();

    // Print the table header
    PRINT_HEADER();

    // Testing various NaN-boxed inputs for square root
    TEST_FSQRT_OP(f0, f1, fsqrt.s, 0, 0, "Test sqrt(NaN-boxed zero). Expected result: NaN");
    TEST_FSQRT_OP(f1, f2, fsqrt.s, 1, 1, "Test sqrt(NaN-boxed positive infinity). Expected result: INFINITY");
    TEST_FSQRT_OP(f2, f3, fsqrt.s, 2, 2, "Test sqrt(NaN-boxed negative infinity). Expected result: NaN");
    TEST_FSQRT_OP(f3, f4, fsqrt.s, 3, 3, "Test sqrt(NaN-boxed negative number). Expected result: NaN");
    TEST_FSQRT_OP(f4, f5, fsqrt.s, 4, 4, "Test sqrt(NaN-boxed positive number). Expected result: NaN");
    TEST_FSQRT_OP(f5, f6, fsqrt.s, 5, 5, "Test sqrt(NaN-boxed NaN). Expected result: NaN");

    // Additional tests for normal floating-point numbers
    TEST_FSQRT_OP(f6, f7, fsqrt.s, 6, 6, "Test sqrt(4.0). Expected result: 2.0");
    TEST_FSQRT_OP(f7, f8, fsqrt.s, 7, 7, "Test sqrt(-9.0). Expected result: NaN");
    TEST_FSQRT_OP(f8, f9, fsqrt.s, 8, 8, "Test sqrt(0.0). Expected result: 0.0");
    TEST_FSQRT_OP(f9, f10, fsqrt.s, 9, 9, "Test sqrt(INFINITY). Expected result: INFINITY");
    TEST_FSQRT_OP(f10, f11, fsqrt.s, 10, 10, "Test sqrt(-INFINITY). Expected result: NaN");
    TEST_FSQRT_OP(f11, f12, fsqrt.s, 11, 11, "Test sqrt(NAN). Expected result: NaN");

    // Additional test case to cover the specific issue scenario
    TEST_FSQRT_OP(f12, f13, fsqrt.s, 12, 12, "Test sqrt(NaN-boxed zero for issue #2450). Expected result: NaN");

    // Print the test results
    printf("\n");
    if (pass) {
        printf("All NaN-boxed sqrt tests passed.\n\n");
    } else {
        printf("Some NaN-boxed sqrt tests failed.\n\n");
    }

    return 0;
}
