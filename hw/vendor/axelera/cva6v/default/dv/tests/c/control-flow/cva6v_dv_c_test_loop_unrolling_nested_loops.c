#include "common.h"  // Include the common header file

__attribute__((section(".data"))) char result_str[20];
__attribute__((section(".data"))) char expected_str[20];

// Function prototype
__attribute__((section(".text"))) void test_loop_unrolling_bug();

__attribute__((section(".text.init"))) int main() {
    PRINT_HEADER();
    test_loop_unrolling_bug();
    return 0;
}

// Function to test a previously known bug related to loop unrolling
__attribute__((section(".text"))) void test_loop_unrolling_bug() {
    const char *scenario = "Loop unrolling bug test";
    volatile int result = 0;
    int expected = 90;  // Corrected expected result to 90
    int i;

    // Loop unrolling might lead to unexpected behavior
    for (i = 0; i < 10; i++) {
        result += i;
    }
    for (i = 0; i < 10; i++) {
        result += i;
    }

    // Convert integers to strings
    int_to_str(result, result_str);
    int_to_str(expected, expected_str);

    // Check if the result matches the expected value
    PRINT_RESULT(scenario, result_str, expected_str, result == expected ? "PASS" : "FAIL");
}
