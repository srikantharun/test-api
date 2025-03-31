#include "common.h"  // Include the common header file

__attribute__((section(".data"))) char result_str[20];
__attribute__((section(".data"))) char expected_str[20];

// Function prototype
__attribute__((section(".text"))) void test_corner_case_overflow();

__attribute__((section(".text.init"))) int main() {
    PRINT_HEADER();
    test_corner_case_overflow();
    return 0;
}

// Function to test corner cases of nested loops with potential overflow
__attribute__((section(".text"))) void test_corner_case_overflow() {
    const char *scenario = "Corner case overflow in nested loops";
    volatile int result = 0;
    int expected = 0x7FFFFFFF;  // Simulate a possible overflow
    int i, j;

    // Nested loop that might cause overflow
    for (i = 0; i < 100; i++) {
        for (j = 0; j < 100; j++) {
            result += i + j;
            if (result < 0) {  // Detect overflow
                result = expected;
                break;
            }
        }
        if (result == expected) break;
    }

    // Convert integers to strings
    int_to_str(result, result_str);
    int_to_str(expected, expected_str);

    // Check if the result matches the expected overflow condition
    PRINT_RESULT(scenario, result_str, expected_str, result == expected ? "PASS" : "FAIL");
}
