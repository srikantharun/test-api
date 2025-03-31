// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, all possible load and store operations are explicitly tested.

#include "common.h"

// Define arrays to store the test values for load and store operations
__attribute__((aligned(8))) uint64_t test_data[16];  // Data used for load and store tests
uint64_t expected_load_results[16];                  // Expected results after load operations

// Function to initialize values for testing load and store operations
void initialize_load_store_values() {
    // Initialize values with different alignment patterns
    test_data[0] = 0x123456789ABCDEF0; // Base case
    test_data[1] = 0x0F0F0F0F0F0F0F0F; // Patterned data
    test_data[2] = 0xFFFFFFFFFFFFFFFF; // All bits set
    test_data[3] = 0x0000000000000000; // All bits clear
    test_data[4] = 0x8000000000000001; // High and low bits set
    test_data[5] = 0x7FFFFFFFFFFFFFFE; // High bit clear, low bits set
    test_data[6] = 0xAAAAAAAAAAAAAAAA; // Alternating bits
    test_data[7] = 0x5555555555555555; // Complement alternating bits
    test_data[8] = 0x0123456789ABCDEF; // Random pattern
    test_data[9] = 0xFEDCBA9876543210; // Reverse pattern
    test_data[10] = 0x0F0F0F0F0F0F0F0F; // Repeated byte pattern
    test_data[11] = 0xF0F0F0F0F0F0F0F0; // Inverted repeated byte pattern
    test_data[12] = 0xFFFFFFFF00000000; // High half set
    test_data[13] = 0x00000000FFFFFFFF; // Low half set
    test_data[14] = 0xDEADBEEFCAFEBABE; // Special pattern
    test_data[15] = 0x1234567890ABCDEF; // Another random pattern
}

// Function to reset the values after a test to maintain consistency
void reset_test_data() {
    initialize_load_store_values();
}

// Macro to print the raw memory for debugging
#define PRINT_MEMORY(addr, description)                               \
    do {                                                              \
        printf("%s at %p: 0x%016llx\n", description, addr, *addr);    \
    } while (0)

// Macro to perform load test and check the result
#define CHECK_LOAD_OP(dest, expected, idx, scenario)                          \
    do {                                                                      \
        uint64_t dest_val;                                                    \
        asm volatile ("mv %0, " #dest : "=r"(dest_val));                      \
        uint64_t expected_val = expected_load_results[idx];                   \
        const char *outcome = (dest_val != expected_val) ? "FAIL" : "PASS";   \
        printf("dest: 0x%016llx expectation: 0x%016llx %-80s\n", dest_val, expected_val, outcome); \
        if (dest_val != expected_val) pass = 0;                               \
    } while (0)

// Macro to perform the specified load operation with description
#define TEST_LOAD_OP(op, dest, addr, idx, description)                       \
    do {                                                                     \
        printf("%-60s with address=%p using %s, %s: ",                       \
               description, &test_data[idx], #dest, #addr);                  \
        asm volatile (op " " #dest ", (%0)" : : "r"(&test_data[idx]));      \
        CHECK_LOAD_OP(dest, expected_load_results[idx], idx, description);   \
    } while (0)

// Macro to calculate expected values after sub-word store operations
#define UPDATE_EXPECTED_STORE(store_op, value, idx) \
    do { \
        uint64_t orig_value = test_data[idx]; \
        uint64_t modified_value = orig_value; \
        if (strcmp(store_op, "sb") == 0) { \
            modified_value = (orig_value & 0xFFFFFFFFFFFFFF00) | (value & 0xFF); \
        } else if (strcmp(store_op, "sh") == 0) { \
            modified_value = (orig_value & 0xFFFFFFFFFFFF0000) | (value & 0xFFFF); \
        } else if (strcmp(store_op, "sw") == 0) { \
            modified_value = (orig_value & 0xFFFFFFFF00000000) | (value & 0xFFFFFFFF); \
        } else if (strcmp(store_op, "sd") == 0) { \
            modified_value = value; \
        } \
        expected_load_results[idx] = modified_value; \
    } while (0)

// Macro to perform the specified store operation with validation using load
#define TEST_STORE_LOAD_OP(store_op, load_op, src, dest, idx, value, description) \
    do {                                                                     \
        reset_test_data();                                                   \
        printf("%-60s with address=%p using %s: ",                           \
               description, &test_data[idx], #src);                          \
        asm volatile (store_op " " #src ", (%0)" : : "r"(&test_data[idx]));  \
        PRINT_MEMORY(&test_data[idx], "Memory after store");                 \
        UPDATE_EXPECTED_STORE(store_op, value, idx);                         \
        TEST_LOAD_OP(load_op, dest, dest, idx, "Validate store followed by load"); \
    } while (0)

int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the load/store values and expected results
    initialize_load_store_values();

    // Print the table header
    printf("\n%-100s  %-80s\n", "Scenario",  "Result");

    // Testing various load operations with `t0` register
    expected_load_results[0] = test_data[0];  // Set expected value for ld
    TEST_LOAD_OP("ld", t0, t0, 0, "Test load doubleword (ld). Expected result: 0x123456789ABCDEF0.");

    expected_load_results[1] = 0x000000000F0F0F0F; // Set expected value for lw
    TEST_LOAD_OP("lw", t0, t0, 1, "Test load word (lw) with patterned data. Expected result: 0x000000000F0F0F0F.");

    expected_load_results[2] = 0xFFFFFFFFFFFFFFFF; // Set expected value for lh
    TEST_LOAD_OP("lh", t0, t0, 2, "Test load halfword (lh) with all bits set. Expected result: 0xFFFFFFFFFFFFFFFF.");

    expected_load_results[3] = 0x0000000000000000; // Set expected value for lhu
    TEST_LOAD_OP("lhu", t0, t0, 3, "Test load halfword unsigned (lhu). Expected result: 0x0000000000000000.");

    expected_load_results[4] = 0xFFFFFFFF80000001; // Set expected value for lb
    TEST_LOAD_OP("lb", t0, t0, 4, "Test load byte (lb). Expected result: 0xFFFFFFFF80000001.");

    expected_load_results[5] = 0x00000000000000FE; // Set expected value for lbu
    TEST_LOAD_OP("lbu", t0, t0, 5, "Test load byte unsigned (lbu). Expected result: 0x00000000000000FE.");

    expected_load_results[6] = 0x00000000000000AA; // Set expected value for lbu
    TEST_LOAD_OP("lbu", t0, t0, 6, "Test load byte unsigned (lbu). Expected result: 0x00000000000000AA.");

    expected_load_results[7] = 0x0000000000000055; // Set expected value for lbu
    TEST_LOAD_OP("lbu", t0, t0, 7, "Test load byte unsigned (lbu). Expected result: 0x0000000000000055.");

    // Testing store operations combined with load validations
    TEST_STORE_LOAD_OP("sd", "ld", t1, t1, 5, 0x0000000000000011, "Store doubleword (sd) followed by load doubleword (ld).");
    TEST_STORE_LOAD_OP("sw", "lw", t1, t1, 6, 0x0000000000000011, "Store word (sw) followed by load word (lw).");
    TEST_STORE_LOAD_OP("sh", "lh", t1, t1, 7, 0x0000000000000011, "Store halfword (sh) followed by load halfword (lh).");
    TEST_STORE_LOAD_OP("sb", "lb", t1, t1, 8, 0x0000000000000011, "Store byte (sb) followed by load byte (lb).");
    TEST_STORE_LOAD_OP("sb", "lb", t1, t1, 9, 0x0000000000000011, "Store byte (sb) followed by load byte (lb).");
    TEST_STORE_LOAD_OP("sh", "lh", t1, t1, 10, 0x0000000000000011, "Store halfword (sh) followed by load halfword (lh).");

    // Additional alignment and pattern checks for load operations
    expected_load_results[10] = 0x0F0F0F0F0F0F0F0F; // Set expected value for ld
    TEST_LOAD_OP("ld", t2, t2, 10, "Test load doubleword (ld) with repeated byte pattern. Expected result: 0x0F0F0F0F0F0F0F0F.");

    expected_load_results[11] = 0xF0F0F0F0F0F0F0F0; // Set expected value for ld
    TEST_LOAD_OP("ld", t2, t2, 11, "Test load doubleword (ld) with inverted repeated byte pattern. Expected result: 0xF0F0F0F0F0F0F0F0.");

    expected_load_results[12] = 0xFFFFFFFF00000000; // Set expected value for ld
    TEST_LOAD_OP("ld", t2, t2, 12, "Test load doubleword (ld) with high half set. Expected result: 0xFFFFFFFF00000000.");

    expected_load_results[13] = 0x00000000FFFFFFFF; // Set expected value for ld
    TEST_LOAD_OP("ld", t2, t2, 13, "Test load doubleword (ld) with low half set. Expected result: 0x00000000FFFFFFFF.");

    expected_load_results[14] = 0xDEADBEEFCAFEBABE; // Set expected value for ld
    TEST_LOAD_OP("ld", t2, t2, 14, "Test load doubleword (ld) with special pattern. Expected result: 0xDEADBEEFCAFEBABE.");

    expected_load_results[15] = 0x1234567890ABCDEF; // Set expected value for ld
    TEST_LOAD_OP("ld", t2, t2, 15, "Test load doubleword (ld) with another random pattern. Expected result: 0x1234567890ABCDEF.");

    // Print the test results
    printf("\n");
    if (pass) {
        printf("All load and store tests passed.\n\n");
    } else {
        printf("Some load and store tests failed.\n\n");
    }

    return 0;
}
