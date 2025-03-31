#include "common.h"  // Include the common header file

__attribute__((section(".data"))) char result_str[20];
__attribute__((section(".data"))) char expected_str[20];

// Function prototype
__attribute__((section(".text"))) void test_classic_nested_loops();

__attribute__((section(".text.init"))) int main() {
    PRINT_HEADER();
    test_classic_nested_loops();
    return 0;
}

// Function to test classic nested loops
__attribute__((section(".text"))) void test_classic_nested_loops() {
    const char *scenario = "Classic nested loops";
    int i, j;
    volatile int result = 0;
    int expected = 0;

    // Nested loop
    for (i = 0; i < 10; i++) {
        for (j = 0; j < 10; j++) {
            result += i + j;
        }
    }

    // Calculate expected result
    for (i = 0; i < 10; i++) {
        for (j = 0; j < 10; j++) {
            expected += i + j;
        }
    }

    // Convert integers to strings
    int_to_str(result, result_str);
    int_to_str(expected, expected_str);

    // Check if the result matches the expected value
    PRINT_RESULT(scenario, result_str, expected_str, result == expected ? "PASS" : "FAIL");
}
