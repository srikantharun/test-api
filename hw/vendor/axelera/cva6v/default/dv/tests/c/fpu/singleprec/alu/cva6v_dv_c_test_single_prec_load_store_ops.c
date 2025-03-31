// This is an extended test file for single_precision_load_store
// CVA6V directed C tests : Author Abhilash Chadhar
// In this test file, various rigorous and corner cases for single-precision floating-point load and store operations are tested,
// focusing on common and complex load/store scenarios. This test avoids cases that trigger trap handlers.

#include "common.h"

// Declare the floating-point values array
float float_values[12]; // Store input test values
float load_store_results[12]; // Store load results for comparison

// Function to initialize floating-point values
void initialize_float_values() {
    float_values[0] = 0.0f;               // 0x00000000 Zero
    float_values[1] = -0.0f;              // 0x80000000 Negative Zero
    float_values[2] = 1.0f;               // 0x3F800000 Normal positive
    float_values[3] = -1.0f;              // 0xBF800000 Normal negative
    float_values[4] = 1.5f;               // 0x3FC00000 Positive fractional
    float_values[5] = -1.5f;              // 0xBFC00000 Negative fractional
    float_values[6] = 1e-30f;             // 0x00CFD70A Small positive denormalized number
    float_values[7] = -1e-30f;            // 0x80CFD70A Small negative denormalized number
    float_values[8] = 1e30f;              // 0x7E37E43C Large positive number
    float_values[9] = -1e30f;             // 0xFE37E43C Large negative number
    float_values[10] = 123.456f;          // 0x42F6E979 Typical positive floating-point value
    float_values[11] = -654.321f;         // 0xC44A58B0 Typical negative floating-point value
}

// Macro to perform load and store operations and check the result
#define TEST_LOAD_STORE(idx, scenario)                                           \
    do {                                                                         \
        asm volatile ("flw fa0, %0" :: "m"(float_values[idx]));                  \
        asm volatile ("fsw fa0, %0" : "=m"(load_store_results[idx]));            \
        float stored_val = load_store_results[idx];                              \
        float original_val = float_values[idx];                                  \
        char original_str[50], stored_str[50];                                   \
        float_to_str(original_val, original_str, 6);                             \
        float_to_str(stored_val, stored_str, 6);                                 \
        const char *result = (fabsf(stored_val - original_val) <= FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        PRINT_LOAD_STORE_RESULT(idx, scenario, original_val, stored_val, result);\
        CHECK_TRUE(fabsf(stored_val - original_val) <= FLOAT_TOLERANCE,          \
            "[CHECK FAILED] %s: Expected '%s', Was '%s'", scenario, original_str, stored_str); \
    } while(0)

int main() {
    testcase_init(); // Initialize test case counters

    // Initialize the floating-point values
    initialize_float_values();

    // Print table header
    PRINT_HEADER();

    // Test scenarios

    // Basic load/store tests
    TEST_LOAD_STORE(0, "Basic Zero Load/Store");
    TEST_LOAD_STORE(1, "Negative Zero Load/Store");
    TEST_LOAD_STORE(2, "Simple Positive Value Load/Store");
    TEST_LOAD_STORE(3, "Simple Negative Value Load/Store");

    // Small denormalized numbers (edge cases)
    TEST_LOAD_STORE(6, "Small Positive Denormalized Number Load/Store");
    TEST_LOAD_STORE(7, "Small Negative Denormalized Number Load/Store");

    // Large numbers (edge cases)
    TEST_LOAD_STORE(8, "Large Positive Number Load/Store");
    TEST_LOAD_STORE(9, "Large Negative Number Load/Store");

    // Typical floating-point values
    TEST_LOAD_STORE(10, "Typical Positive Floating-Point Value Load/Store");
    TEST_LOAD_STORE(11, "Typical Negative Floating-Point Value Load/Store");

    // Complex scenarios: Storing to different registers
    asm volatile ("flw fa1, %0" :: "m"(float_values[10]));  // Load into fa1
    asm volatile ("fsw fa1, %0" : "=m"(load_store_results[10])); // Store fa1
    TEST_LOAD_STORE(10, "Load into fa1, Store from fa1");

    asm volatile ("flw fa2, %0" :: "m"(float_values[11]));  // Load into fa2
    asm volatile ("fsw fa2, %0" : "=m"(load_store_results[11])); // Store fa2
    TEST_LOAD_STORE(11, "Load into fa2, Store from fa2");

    // Misaligned addresses (without trap) : TODO Enable this in error scenarios
    //float *unaligned_address = (float*)((char*)float_values + 1);
    //asm volatile ("flw fa0, %0" :: "m"(*unaligned_address));
    //asm volatile ("fsw fa0, %0" : "=m"(load_store_results[0]));
    //TEST_LOAD_STORE(0, "Misaligned Address (No Trap)");

    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All load/store tests passed.\n");
    } else {
        printf("Some load/store tests failed.\n");
    }

    return 0;
}
