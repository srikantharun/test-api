/*
 * single_prec_fp_compare_test.c - Comprehensive test for RISC-V CVA6 single-precision FP comparison instructions
 */

#include "testutils.h"
#include <common.h>
#include <stdint.h>
#include <stdbool.h>

// Declare external symbols for tohost interface
extern volatile uint64_t tohost;

// Helper function to convert uint32_t bit patterns to float
static inline float uint32_to_float(uint32_t x) {
    union {
        uint32_t u;
        float f;
    } converter;
    converter.u = x;
    return converter.f;
}

// Define floating-point constants using bit patterns ensuring proper alignment

// Floating-point constants are now defined using bit patterns directly in the test cases

// Helper functions to perform comparisons using inline assembly
static inline int feq_s(float a, float b) {
    int result;
    asm volatile("feq.s %0, %1, %2"
                 : "=r"(result)
                 : "f"(a), "f"(b));
    return result;
}

static inline int flt_s(float a, float b) {
    int result;
    asm volatile("flt.s %0, %1, %2"
                 : "=r"(result)
                 : "f"(a), "f"(b));
    return result;
}

static inline int fle_s(float a, float b) {
    int result;
    asm volatile("fle.s %0, %1, %2"
                 : "=r"(result)
                 : "f"(a), "f"(b));
    return result;
}

// Test case structure with uint32_t bit patterns
typedef struct {
    const char *description;
    uint32_t a_bits;
    uint32_t b_bits;
    int expected_eq;
    int expected_lt;
    int expected_le;
} fp_compare_test_t;

// Define all feq.s test cases using bit patterns
static const fp_compare_test_t feq_tests[] = {
    // Normal numbers
    {"feq.s: 1.0 == 1.0", 0x3F800000, 0x3F800000, 1, 0, 1},
    {"feq.s: 1.0 == 2.0", 0x3F800000, 0x40000000, 0, 1, 1},
    {"feq.s: 2.0 == 1.0", 0x40000000, 0x3F800000, 0, 0, 0},

    // Zeros
    {"feq.s: +0.0 == +0.0", 0x00000000, 0x00000000, 1, 0, 1},
    {"feq.s: -0.0 == -0.0", 0x80000000, 0x80000000, 1, 0, 1},
    {"feq.s: +0.0 == -0.0", 0x00000000, 0x80000000, 1, 0, 1},
    {"feq.s: -0.0 == +0.0", 0x80000000, 0x00000000, 1, 0, 1},

    // Subnormals
    {"feq.s: subnormal == subnormal", 0x00000001, 0x00000001, 1, 0, 1},
    {"feq.s: subnormal == 1.0", 0x00000001, 0x3F800000, 0, 1, 1},

    // Infinities
    {"feq.s: +inf == +inf", 0x7F800000, 0x7F800000, 1, 0, 1},
    {"feq.s: -inf == -inf", 0xFF800000, 0xFF800000, 1, 0, 1},
    {"feq.s: +inf == -inf", 0x7F800000, 0xFF800000, 0, 0, 0},

    // NaNs
    {"feq.s: NaN == NaN", 0x7FC00000, 0x7FC00000, 0, 0, 0},
    {"feq.s: NaN == 1.0", 0x7FC00000, 0x3F800000, 0, 0, 0},
    {"feq.s: 1.0 == NaN", 0x3F800000, 0x7FC00000, 0, 0, 0},

    // Signaling NaNs (if supported)
    {"feq.s: sNaN == sNaN", 0x7FA00000, 0x7FA00000, 0, 0, 0},
};

// Define all flt.s test cases using bit patterns
static const fp_compare_test_t flt_tests_cases[] = {
    // Normal numbers
    {"flt.s: 1.0 < 2.0", 0x3F800000, 0x40000000, 0, 1, 1},
    {"flt.s: 2.0 < 1.0", 0x40000000, 0x3F800000, 0, 0, 0},
    {"flt.s: 1.0 < 1.0", 0x3F800000, 0x3F800000, 0, 0, 1},

    // Zeros
    {"flt.s: +0.0 < +0.0", 0x00000000, 0x00000000, 0, 0, 0},
    {"flt.s: -0.0 < -0.0", 0x80000000, 0x80000000, 0, 0, 0},
    {"flt.s: +0.0 < -0.0", 0x00000000, 0x80000000, 0, 0, 0},
    {"flt.s: -0.0 < +0.0", 0x80000000, 0x00000000, 0, 0, 0},

    // Subnormals
    {"flt.s: subnormal < 1.0", 0x00000001, 0x3F800000, 0, 1, 1},
    {"flt.s: 1.0 < subnormal", 0x3F800000, 0x00000001, 0, 0, 0},
    {"flt.s: subnormal < subnormal", 0x00000001, 0x00000001, 0, 0, 0},

    // Infinities
    {"flt.s: 1.0 < +inf", 0x3F800000, 0x7F800000, 0, 1, 1}, // 1.0 < +inf
    {"flt.s: +inf < 1.0", 0x7F800000, 0x3F800000, 0, 0, 0},
    {"flt.s: +inf < +inf", 0x7F800000, 0x7F800000, 0, 0, 0},
    {"flt.s: -inf < -inf", 0xFF800000, 0xFF800000, 0, 0, 0},
    {"flt.s: -inf < 1.0", 0xFF800000, 0x3F800000, 0, 1, 1}, // Corrected expected_eq to 0
    {"flt.s: 1.0 < -inf", 0x3F800000, 0xFF800000, 0, 0, 0},

    // NaNs
    {"flt.s: NaN < 1.0", 0x7FC00000, 0x3F800000, 0, 0, 0},
    {"flt.s: 1.0 < NaN", 0x3F800000, 0x7FC00000, 0, 0, 0},
    {"flt.s: NaN < NaN", 0x7FC00000, 0x7FC00000, 0, 0, 0},

    // Signaling NaNs (if supported)
    {"flt.s: sNaN < 1.0", 0x7FA00000, 0x3F800000, 0, 0, 0},
    {"flt.s: 1.0 < sNaN", 0x3F800000, 0x7FA00000, 0, 0, 0},
};

// Define all fle.s test cases using bit patterns
static const fp_compare_test_t fle_tests_cases[] = {
    // Normal numbers
    {"fle.s: 1.0 <= 2.0", 0x3F800000, 0x40000000, 0, 1, 1},
    {"fle.s: 2.0 <= 1.0", 0x40000000, 0x3F800000, 0, 0, 0},
    {"fle.s: 1.0 <= 1.0", 0x3F800000, 0x3F800000, 1, 0, 1},

    // Zeros
    {"fle.s: +0.0 <= +0.0", 0x00000000, 0x00000000, 1, 0, 1},
    {"fle.s: -0.0 <= -0.0", 0x80000000, 0x80000000, 1, 0, 1},
    {"fle.s: +0.0 <= -0.0", 0x00000000, 0x80000000, 1, 0, 1},
    {"fle.s: -0.0 <= +0.0", 0x80000000, 0x00000000, 1, 0, 1},

    // Subnormals
    {"fle.s: subnormal <= 1.0", 0x00000001, 0x3F800000, 0, 1, 1},
    {"fle.s: 1.0 <= subnormal", 0x3F800000, 0x00000001, 0, 0, 0},
    {"fle.s: subnormal <= subnormal", 0x00000001, 0x00000001, 1, 0, 1},

    // Infinities
    {"fle.s: 1.0 <= +inf", 0x3F800000, 0x7F800000, 0, 1, 1}, // 1.0 <= +inf
    {"fle.s: +inf <= 1.0", 0x7F800000, 0x3F800000, 0, 0, 0},
    {"fle.s: +inf <= +inf", 0x7F800000, 0x7F800000, 1, 0, 1},
    {"fle.s: -inf <= -inf", 0xFF800000, 0xFF800000, 1, 0, 1},
    {"fle.s: -inf <= 1.0", 0xFF800000, 0x3F800000, 0, 1, 1},
    {"fle.s: 1.0 <= -inf", 0x3F800000, 0xFF800000, 0, 0, 0},

    // NaNs
    {"fle.s: NaN <= 1.0", 0x7FC00000, 0x3F800000, 0, 0, 0},
    {"fle.s: 1.0 <= NaN", 0x3F800000, 0x7FC00000, 0, 0, 0},
    {"fle.s: NaN <= NaN", 0x7FC00000, 0x7FC00000, 0, 0, 0},

    // Signaling NaNs (if supported)
    {"fle.s: sNaN <= 1.0", 0x7FA00000, 0x3F800000, 0, 0, 0},
    {"fle.s: 1.0 <= sNaN", 0x3F800000, 0x7FA00000, 0, 0, 0},
};

// Function to run feq.s tests
void run_feq_tests(void) {
    size_t num_tests = sizeof(feq_tests) / sizeof(fp_compare_test_t);
    for (size_t i = 0; i < num_tests; i++) {
        const fp_compare_test_t *test = &feq_tests[i];
        float a = uint32_to_float(test->a_bits);
        float b = uint32_to_float(test->b_bits);
        int result = feq_s(a, b);
        CHECK_EQUAL_INT(test->expected_eq, result, "%s", test->description);
    }
}

// Function to run flt.s tests
void run_flt_tests(void) {
    size_t num_tests = sizeof(flt_tests_cases) / sizeof(fp_compare_test_t);
    for (size_t i = 0; i < num_tests; i++) {
        const fp_compare_test_t *test = &flt_tests_cases[i];
        float a = uint32_to_float(test->a_bits);
        float b = uint32_to_float(test->b_bits);
        int result = flt_s(a, b);
        CHECK_EQUAL_INT(test->expected_lt, result, "%s", test->description);
    }
}

// Function to run fle.s tests
void run_fle_tests(void) {
    size_t num_tests = sizeof(fle_tests_cases) / sizeof(fp_compare_test_t);
    for (size_t i = 0; i < num_tests; i++) {
        const fp_compare_test_t *test = &fle_tests_cases[i];
        float a = uint32_to_float(test->a_bits);
        float b = uint32_to_float(test->b_bits);
        int result = fle_s(a, b);
        CHECK_EQUAL_INT(test->expected_le, result, "%s", test->description);
    }
}

int main(void) {
    // Initialize test framework
    testcase_init();

    // Run all comparison tests
    run_feq_tests();
    run_flt_tests();
    run_fle_tests();

    // Finalize test and get result
    int result = testcase_finalize();

    // Write result to tohost
    if (result == TEST_SUCCESS) {
        tohost = 1; // Success code
    } else {
        tohost = -1; // Failure code
    }

    // Optionally, you can loop indefinitely after reporting
    while (1) {
        // Wait for host to collect the result
        __asm__ volatile("wfi");
    }

    return result;
}
