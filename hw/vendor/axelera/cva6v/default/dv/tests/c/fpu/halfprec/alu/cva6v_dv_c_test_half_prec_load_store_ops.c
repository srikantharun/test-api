#include "common.h"

// Declare the half-precision floating-point values array
uint16_t half_float_values[12] __attribute__((section(".data"), aligned(64))); // Store input test values
uint16_t load_store_results[12] __attribute__((section(".data"), aligned(64))); // Store load results for comparison

// Function to initialize half-precision floating-point values
__attribute__((section(".text"), aligned(64)))
void initialize_half_float_values() {
    half_float_values[0] = 0x0000; // Zero
    half_float_values[1] = 0x8000; // Negative Zero
    half_float_values[2] = 0x3C00; // 1.0 (Normal positive)
    half_float_values[3] = 0xBC00; // -1.0 (Normal negative)
    half_float_values[4] = 0x3E00; // 1.5 (Positive fractional)
    half_float_values[5] = 0xBE00; // -1.5 (Negative fractional)
    half_float_values[6] = 0x0400; // Small positive denormalized number
    half_float_values[7] = 0x8400; // Small negative denormalized number
    half_float_values[8] = 0x7BFF; // Large positive number
    half_float_values[9] = 0xFBFF; // Large negative number
    half_float_values[10] = 0x55C2; // Typical positive half-precision value (~123.456)
    half_float_values[11] = 0xE5A2; // Typical negative half-precision value (~-654.321)
}

// Macro to perform a single load and store operation
#define LOAD_STORE_OPERATION(register, index) \
    asm volatile ("flh " register ", %0" :: "m"(half_float_values[index])); \
    asm volatile ("fsh " register ", %0" : "=m"(load_store_results[index]));

// Macro to test a specific scenario
#define TEST_LOAD_STORE_HALF(idx, scenario)                                      \
    do {                                                                         \
        LOAD_STORE_OPERATION("fa0", idx)                                         \
        float stored_val = half_to_float(load_store_results[idx]);               \
        float original_val = half_to_float(half_float_values[idx]);              \
        const char *result = (fabsf(stored_val - original_val) <= HALF_FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        PRINT_LOAD_STORE_RESULT(idx, scenario, original_val, stored_val, result);\
        if (strcmp(result, "FAIL") == 0) pass = 0;                               \
    } while(0)

// Macro to handle complex load/store scenarios involving multiple registers
#define TEST_COMPLEX_LOAD_STORE(register1, register2, idx1, idx2, scenario)      \
    do {                                                                         \
        asm volatile ("flh " register1 ", %0" :: "m"(half_float_values[idx1]));  \
        asm volatile ("fsh " register1 ", %0" : "=m"(load_store_results[idx1])); \
        asm volatile ("flh " register2 ", %0" :: "m"(load_store_results[idx1])); \
        asm volatile ("fsh " register2 ", %0" : "=m"(load_store_results[idx2])); \
        TEST_LOAD_STORE_HALF(idx2, scenario);                                    \
    } while(0)

__attribute__((section(".text"), aligned(64)))
int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the half-precision floating-point values
    initialize_half_float_values();

    // Print table header
    PRINT_HEADER();

    // Basic load/store tests
    TEST_LOAD_STORE_HALF(0, "Basic Zero Load/Store");
    TEST_LOAD_STORE_HALF(1, "Negative Zero Load/Store");
    TEST_LOAD_STORE_HALF(2, "Simple Positive Value Load/Store");
    TEST_LOAD_STORE_HALF(3, "Simple Negative Value Load/Store");

    // Small denormalized numbers (edge cases)
    TEST_LOAD_STORE_HALF(6, "Small Positive Denormalized Number Load/Store");
    TEST_LOAD_STORE_HALF(7, "Small Negative Denormalized Number Load/Store");

    // Large numbers (edge cases)
    TEST_LOAD_STORE_HALF(8, "Large Positive Number Load/Store");
    TEST_LOAD_STORE_HALF(9, "Large Negative Number Load/Store");

    // Typical floating-point values
    TEST_LOAD_STORE_HALF(10, "Typical Positive Half-Precision Value Load/Store");
    TEST_LOAD_STORE_HALF(11, "Typical Negative Half-Precision Value Load/Store");

    // Complex scenarios: Storing to different registers
    TEST_COMPLEX_LOAD_STORE("fa1", "fa0", 10, 11, "Load into fa1, Store from fa1");
    TEST_COMPLEX_LOAD_STORE("fa2", "fa0", 11, 10, "Load into fa2, Store from fa2"); // Added missing scenario

    // More complex load/store sequences
    TEST_COMPLEX_LOAD_STORE("fa0", "fa3", 2, 3, "Store, Load, Store Sequence");
    TEST_COMPLEX_LOAD_STORE("fa1", "fa2", 4, 5, "Load, Load, Store Redundant Loads");
    TEST_COMPLEX_LOAD_STORE("fa3", "fa4", 6, 7, "Store, Load, Store Sequence"); // Added missing scenario
    TEST_COMPLEX_LOAD_STORE("fa5", "fa6", 0, 1, "Load, Load, Store Redundant Loads"); // Added missing scenario

    // Unaligned Access Test
    uint16_t unaligned_data[5] __attribute__((aligned(2))) = {0x3C00, 0xBC00, 0x3E00, 0xBE00, 0x0400};
    asm volatile ("flh fa0, %0" :: "m"(unaligned_data[1]));       // Unaligned load
    asm volatile ("fsh fa0, %0" : "=m"(unaligned_data[2]));       // Unaligned store
    TEST_LOAD_STORE_HALF(5, "Unaligned Memory Access");

    asm volatile ("flh fa1, %0" :: "m"(unaligned_data[3]));       // Additional unaligned load
    asm volatile ("fsh fa1, %0" : "=m"(unaligned_data[4]));       // Additional unaligned store
    TEST_LOAD_STORE_HALF(6, "Unaligned Memory Access Additional"); // Added missing scenario

    // Load-Store Dependency Chain
    TEST_COMPLEX_LOAD_STORE("fa0", "fa1", 5, 7, "Load-Store Dependency Chain");
    TEST_COMPLEX_LOAD_STORE("fa2", "fa3", 6, 8, "Load-Store Dependency Chain Additional"); // Added missing scenario

    // Overlapping Memory Region
    uint16_t overlapping_data[4] __attribute__((aligned(64))) = {0x3C00, 0xBC00, 0x3E00, 0xBE00};
    asm volatile ("flh fa2, %0" :: "m"(overlapping_data[1]));     // Load from overlapping region
    asm volatile ("fsh fa2, %0" : "=m"(overlapping_data[2]));     // Store to overlapping region
    TEST_LOAD_STORE_HALF(8, "Overlapping Memory Region Load/Store");

    asm volatile ("flh fa3, %0" :: "m"(overlapping_data[0]));     // Additional overlapping load
    asm volatile ("fsh fa3, %0" : "=m"(overlapping_data[3]));     // Additional overlapping store
    TEST_LOAD_STORE_HALF(9, "Overlapping Memory Region Load/Store Additional"); // Added missing scenario

    // Sequential Load and Store with All Registers
    LOAD_STORE_OPERATION("fa0", 0)
    LOAD_STORE_OPERATION("fa1", 1)
    LOAD_STORE_OPERATION("fa2", 2)
    LOAD_STORE_OPERATION("fa3", 3)
    LOAD_STORE_OPERATION("fa4", 4)
    LOAD_STORE_OPERATION("fa5", 5)
    LOAD_STORE_OPERATION("fa6", 6)
    LOAD_STORE_OPERATION("fa7", 7)

    TEST_LOAD_STORE_HALF(9, "Sequential Load and Store with All Registers");

    TEST_LOAD_STORE_HALF(10, "Sequential Load and Store with All Registers Additional"); // Added missing scenario

    if (pass) {
        printf("All half-precision load/store tests passed.\n");
    } else {
        printf("Some half-precision load/store tests failed.\n");
    }

    return 0;
}
