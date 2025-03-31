// CVA6V directed C tests for counters and timers: Author: Abhilash Chadhar
// In this test file, base counters and timers are explicitly tested.

#include "common.h"

// Define variables to store test values and previous values
uint64_t previous_values[5]; // To store previous counter values

// Define the memory-mapped address for mtime with proper alignment
volatile uint64_t *mtime_addr = (uint64_t *)0x200000BFF8; // Adjusted memory address for alignment

// Function to initialize values for testing counters and timers
void initialize_previous_values() {
    // Initialize previous values for counters
    previous_values[0] = 0; // Initial previous value for cycle counter
    previous_values[1] = 0; // Initial previous value for instruction retired counter
    previous_values[2] = 0; // Initial previous value for time counter
    previous_values[3] = 0; // Initial previous value for mtime
}

// Macro to perform counter read and check if it increments correctly within a range
#define CHECK_COUNTER(csr_number, idx, scenario)                              \
    do {                                                                      \
        uint64_t result_val;                                                  \
        char result_str[50], expected_str[50];                                \
        if (csr_number == CSR_MTIME) {                                        \
            result_val = *mtime_addr; /* Read mtime from memory-mapped address */ \
        } else {                                                              \
            asm volatile ("csrr %0, %1" : "=r"(result_val) : "i"(csr_number));\
        }                                                                     \
        uint64_to_str(result_val, result_str);                                \
        uint64_to_str(previous_values[idx], expected_str);                    \
        /* Check if the counter has incremented within a reasonable range */  \
        const char* result = (result_val > previous_values[idx]) ? "PASS" : "FAIL"; \
        PRINT_RESULT(scenario, result_str, expected_str, result);             \
        if (strcmp(result, "FAIL") == 0) pass = 0;                            \
        previous_values[idx] = result_val; /* Update previous value */        \
    } while(0)

// Macro to test counter operations with a description
#define TEST_COUNTER(csr_number, idx, description)                            \
    do {                                                                      \
        /* Perform a counter read test */                                     \
        CHECK_COUNTER(csr_number, idx, description);                          \
    } while(0)

// CSR register numbers
#define CSR_MTIME    0x701 // Only for reference; use memory-mapped access

int main() {
    int pass = 1; // Assume all tests pass unless a test fails

    // Initialize previous counter values
    initialize_previous_values();

    // Print the table header
    PRINT_HEADER();

    // Testing counter operations with explanations
    TEST_COUNTER(CSR_CYCLE, 0, "Test increment of cycle counter (rdcycle): dest_val should be greater than expected");
    TEST_COUNTER(CSR_INSTRET, 1, "Test increment of instruction retired counter (rdinstret): dest_val should be greater than expected");
    TEST_COUNTER(CSR_TIME, 2, "Test increment of time counter (rdtime): dest_val should be greater than expected");
    TEST_COUNTER(CSR_MTIME, 3, "Test increment of machine timer (mtime): dest_val should be greater than expected");

    // Stress test for increment consistency
    for (int i = 0; i < 10; i++) {
        TEST_COUNTER(CSR_CYCLE, 0, "Stress test cycle counter increment under load: dest_val should be greater than expected");
        TEST_COUNTER(CSR_INSTRET, 1, "Stress test instruction retired counter increment under load: dest_val should be greater than expected");
        TEST_COUNTER(CSR_TIME, 2, "Stress test time counter increment under load: dest_val should be greater than expected");
    }

    // Print the test results
    if (pass) {
        printf("All counter and timer tests passed.\n");
    } else {
        printf("Some counter or timer tests failed.\n");
    }

    return 0;
}
