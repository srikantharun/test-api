// Test file for move and type-conversion half-precision floating-point operations
// CVA6V directed C tests: Author:  Abhilash Chadhar
// In this test file, the following floating-point operations are explicitly tested:
// fmv.x.h - Move half-precision floating-point to 32-bit integer
// fmv.h.x - Move 32-bit integer to half-precision floating-point
// fmv.h - Move half-precision floating-point value between registers

#include "common.h"

// Define arrays to store the test values
uint16_t half_float_values[13] __attribute__((section(".data"), aligned(64)));  // Adjusted to allow extra edge cases like NaN and Infinity
int int_values[13] __attribute__((section(".data"), aligned(64)));
uint16_t expected_half_float_values[13] __attribute__((section(".data"), aligned(64)));
int expected_int_values[13] __attribute__((section(".data"), aligned(64)));

// Function to initialize values for testing
__attribute__((section(".text"), aligned(64)))
void initialize_values() {
    // Initializing half-precision float values for fmv.x.h tests
    half_float_values[0] = 0x0000;              // 0.0f
    half_float_values[1] = 0x8000;              // -0.0f
    half_float_values[2] = 0x4248;              // A common floating-point value (3.140625)
    half_float_values[3] = 0xC248;              // Another common floating-point value (-3.140625)
    half_float_values[4] = 0x03FF;              // Subnormal small positive
    half_float_values[5] = 0x83FF;              // Subnormal small negative
    half_float_values[6] = 0x7BFF;              // Maximum finite half-precision float
    half_float_values[7] = 0xFBFF;              // Maximum finite negative half-precision float

    // Add additional cases for NaN, positive infinity, and negative infinity
    uint16_t nan_value = 0x7E00;
    uint16_t pos_inf_value = 0x7C00;
    uint16_t neg_inf_value = 0xFC00;

    half_float_values[8] = nan_value;
    half_float_values[9] = pos_inf_value;
    half_float_values[10] = neg_inf_value;

    // Initializing integer values for fmv.h.x tests
    int_values[0] = 0x00000000;          // 0
    int_values[1] = 0x80000000;          // Negative zero representation
    int_values[2] = 3;                   // 3.140625 in half-precision float should round to 3
    int_values[3] = -3;                  // -3.140625 in half-precision float should round to -3
    int_values[4] = 0;                   // Subnormal small positive rounds to 0
    int_values[5] = 0;                   // Subnormal small negative rounds to 0
    int_values[6] = 65504;               // Maximum finite half-precision float (65504)
    int_values[7] = -65504;              // Maximum finite negative half-precision float (-65504)

    // Expected results for fmv.x.h and fmv.h.x tests
    for (int i = 0; i < 8; i++) {
        expected_int_values[i] = int_values[i];           // The int representation should match the rounded value
        expected_half_float_values[i] = half_float_values[i]; // The half-float representation should match
    }

    // Set expected values for NaN, Infinity cases
    expected_int_values[8] = 0;                         // NaN -> 0
    expected_int_values[9] = 2147483647;                // Positive infinity -> INT_MAX
    expected_int_values[10] = -2147483648;              // Negative infinity -> INT_MIN

    expected_half_float_values[8] = nan_value;
    expected_half_float_values[9] = pos_inf_value;
    expected_half_float_values[10] = neg_inf_value;
}

// Macro to perform checks
#define CHECK_FMV_X_H(dest, src, idx, scenario)                                \
    do {                                                                       \
        int dest_val;                                                          \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("sw " #dest ", %0" : "=m"(dest_val));                    \
        int expected_val = (half_float_values[idx] == 0x8000) ? 0 : expected_int_values[idx]; /* Handle -0.0f */ \
        int_to_str(dest_val, dest_str);                                        \
        int_to_str(expected_val, expected_str);                                \
        const char* result = (dest_val != expected_val) ? "FAIL" : "PASS";     \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        if (strcmp(result, "FAIL") == 0) pass = 0;                             \
    } while(0)


#define CHECK_FMV_H_X(dest, src, idx, scenario)                                \
    do {                                                                       \
        uint16_t dest_val;                                                     \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("fsh " #dest ", %0" : "=m"(dest_val));                   \
        half_float_to_str(dest_val, dest_str, 6);                              \
        half_float_to_str(expected_half_float_values[idx], expected_str, 6);   \
        const char* result = (fabsf(dest_val - expected_half_float_values[idx]) > HALF_FLOAT_TOLERANCE) ? "FAIL" : "PASS"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        if (strcmp(result, "FAIL") == 0) pass = 0;                             \
    } while(0)


#define CHECK_FMV_H(dest, src, idx, scenario)                                  \
    do {                                                                       \
        uint16_t dest_val;                                                     \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("fsh " #dest ", %0" : "=m"(dest_val));                   \
        half_float_to_str(dest_val, dest_str, 6);                              \
        half_float_to_str(expected_half_float_values[idx], expected_str, 6);   \
        const char* result = (fabsf(dest_val - expected_half_float_values[idx]) > HALF_FLOAT_TOLERANCE) ? "FAIL" : "PASS"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        if (strcmp(result, "FAIL") == 0) pass = 0;                             \
    } while(0)

// Macro to perform fmv.x.h test with scenario description
#define TEST_FMV_X_H(dest, src, idx, description)                              \
    do {                                                                       \
        asm volatile ("flh " #src ", %0" :: "m"(half_float_values[idx]));      \
        asm volatile ("fmv.x.h " #dest ", " #src);                             \
        CHECK_FMV_X_H(dest, src, idx, description);                            \
    } while(0)

// Macro to perform fmv.h.x test with scenario description
#define TEST_FMV_H_X(dest, src, idx, description)                              \
    do {                                                                       \
        asm volatile ("lh " #src ", %0" : : "m"(int_values[idx]));             \
        asm volatile ("fmv.h.x " #dest ", " #src);                             \
        CHECK_FMV_H_X(dest, src, idx, description);                            \
    } while(0)

// Macro to perform fmv.h test with scenario description
#define TEST_FMV_H(dest, src, idx, description)                                \
    do {                                                                       \
        asm volatile ("flh " #src ", %0" :: "m"(half_float_values[idx]));      \
        asm volatile ("fmv.h " #dest ", " #src);                               \
        CHECK_FMV_H(dest, src, idx, description);                              \
    } while(0)

__attribute__((section(".text"), aligned(64)))
int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the floating-point and integer values
    initialize_values();

    // Set rounding mode - "round to nearest"
    asm volatile("li t0, 0b00000000000000000000000000000000; csrw fcsr, t0"); // Set rounding mode

    // Print the table header
    PRINT_HEADER();

    // Testing fmv.x.h (move half-float to int)
    TEST_FMV_X_H(a0, fa0, 0, "Test moving 0.0f to integer");
    TEST_FMV_X_H(a0, fa0, 1, "Test moving -0.0f to integer");
    TEST_FMV_X_H(a0, fa0, 2, "Test moving 3.140625f to integer");
    TEST_FMV_X_H(a0, fa0, 3, "Test moving -3.140625f to integer");
    TEST_FMV_X_H(a0, fa0, 4, "Test moving small positive subnormal to integer");
    TEST_FMV_X_H(a0, fa0, 5, "Test moving small negative subnormal to integer");
    TEST_FMV_X_H(a0, fa0, 6, "Test moving max finite half-float to integer");
    TEST_FMV_X_H(a0, fa0, 7, "Test moving max finite negative half-float to integer");
    TEST_FMV_X_H(a0, fa0, 8, "Test moving NaN to integer (expected 0)");
    TEST_FMV_X_H(a0, fa0, 9, "Test moving +Infinity to integer (expected INT_MAX)");
    TEST_FMV_X_H(a0, fa0, 10, "Test moving -Infinity to integer (expected INT_MIN)");

    // Testing fmv.h.x (move int to half-float)
    TEST_FMV_H_X(fa0, a0, 0, "Test moving 0 to half-float");
    TEST_FMV_H_X(fa0, a0, 1, "Test moving negative zero to half-float");
    TEST_FMV_H_X(fa0, a0, 2, "Test moving 3.140625 as integer to half-float");
    TEST_FMV_H_X(fa0, a0, 3, "Test moving -3.140625 as integer to half-float");
    TEST_FMV_H_X(fa0, a0, 4, "Test moving small positive subnormal as integer to half-float");
    TEST_FMV_H_X(fa0, a0, 5, "Test moving small negative subnormal as integer to half-float");
    TEST_FMV_H_X(fa0, a0, 6, "Test moving max finite half-float as integer to half-float");
    TEST_FMV_H_X(fa0, a0, 7, "Test moving max finite negative half-float as integer to half-float");

    // Testing fmv.h (move half-float between registers)
    TEST_FMV_H(fa1, fa0, 0, "Move 0.0f between registers");
    TEST_FMV_H(fa1, fa0, 1, "Move -0.0f between registers");
    TEST_FMV_H(fa1, fa0, 2, "Move 3.140625f between registers");
    TEST_FMV_H(fa1, fa0, 3, "Move -3.140625f between registers");
    TEST_FMV_H(fa1, fa0, 4, "Move small positive subnormal between registers");
    TEST_FMV_H(fa1, fa0, 5, "Move small negative subnormal between registers");
    TEST_FMV_H(fa1, fa0, 6, "Move max finite half-float between registers");
    TEST_FMV_H(fa1, fa0, 7, "Move max finite negative half-float between registers");

    if (pass) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }

    return 0;
}
