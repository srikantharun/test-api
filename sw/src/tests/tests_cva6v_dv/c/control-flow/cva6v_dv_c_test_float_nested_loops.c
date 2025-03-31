#include "common.h"  // Include the common header file

__attribute__((section(".data"))) char result_str[20];
__attribute__((section(".data"))) char expected_str[20];

// Function prototype
__attribute__((section(".text"))) void test_classic_nested_loops_float();

__attribute__((section(".text.init"))) int main() {
    PRINT_HEADER();
    test_classic_nested_loops_float();
    return 0;
}

// Function to test nested loops with single-precision floats
__attribute__((section(".text"))) void test_classic_nested_loops_float() {
    const char *scenario = "Classic nested loops with floats";
    int i, j;
    volatile float result = 0.0f;
    float expected = 0.0f;

    // Nested loop with floats
    for (i = 0; i < 10; i++) {
        for (j = 0; j < 10; j++) {
            result += (float)(i + j) * 0.1f;  // Use floating-point arithmetic
        }
    }

    // Calculate expected result
    for (i = 0; i < 10; i++) {
        for (j = 0; j < 10; j++) {
            expected += (float)(i + j) * 0.1f;
        }
    }

    // Convert floats to strings
    float_to_str(result, result_str, 6);
    float_to_str(expected, expected_str, 6);

    // Check if the result matches the expected value
    PRINT_RESULT(scenario, result_str, expected_str, fabsf(result - expected) < FLOAT_TOLERANCE ? "PASS" : "FAIL");
}
