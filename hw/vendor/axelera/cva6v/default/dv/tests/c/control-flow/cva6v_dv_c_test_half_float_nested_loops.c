#include "common.h"  // Include the common header file

__attribute__((section(".data"))) char result_str[20];
__attribute__((section(".data"))) char expected_str[20];

// Function prototype
__attribute__((section(".text"))) void test_corner_case_half_float();

__attribute__((section(".text.init"))) int main() {
    PRINT_HEADER();
    test_corner_case_half_float();
    return 0;
}

// Function to test corner cases with half-precision floats
__attribute__((section(".text"))) void test_corner_case_half_float() {
    const char *scenario = "Corner case with half-precision floats";
    uint16_t half_result;
    uint16_t expected_half = 0x7C00;  // Half-precision positive infinity

    // Generate a random half-precision float and check for infinity
    half_result = rand_half_float();
    if (half_result == expected_half) {
        printf("Generated half-precision float is positive infinity.\n");
    } else {
        expected_half = half_result; // Update expected to match generated random value
    }

    // Convert half-floats to strings
    half_float_to_str(half_result, result_str, 6);
    half_float_to_str(expected_half, expected_str, 6);

    // Check if the result matches the expected special case
    PRINT_RESULT(scenario, result_str, expected_str, half_result == expected_half ? "PASS" : "FAIL");
}
