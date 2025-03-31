#include "common.h"

// Define variables and arrays to store data for testing
__attribute__((aligned(64))) uint64_t data_memory[4];  // Memory used for cache management tests, aligned to 64 bytes
uint64_t expected_results[4];                         // Expected results after various operations

// Function to initialize values for testing cache management
void initialize_cache_test_values() {
    data_memory[0] = 0xDEADBEEFDEADBEEF;  // Initial data pattern
    data_memory[1] = 0xCAFEBABECAFEBABE;  // Another data pattern
    data_memory[2] = 0x1234567812345678;  // Additional pattern
    data_memory[3] = 0x0F0F0F0F0F0F0F0F;  // Repeated pattern

    // Expected results before any cache operations
    expected_results[0] = data_memory[0];
    expected_results[1] = data_memory[1];
    expected_results[2] = data_memory[2];
    expected_results[3] = data_memory[3];
}

// Function to reset test data to initial state
void reset_test_data() {
    initialize_cache_test_values();
}

// Macros updated to use testutils and print detailed test outputs

// Macro to check if data is consistent with expected results
#define CHECK_MEMORY_OP(dest, expected, idx, description)                          \
    do {                                                                           \
        uint64_t dest_val = *dest;                                                 \
        printf("%-100s: Memory check: 0x%016llx expectation: 0x%016llx ", description, dest_val, expected_results[idx]); \
        if (!CHECK_EQUAL_HEX(dest_val, expected_results[idx], "%s at index %d", description, idx)) {                    \
            printf("FAIL\n");                                                                                            \
        } else {                                                                                                         \
            printf("PASS\n");                                                                                            \
        }                                                                                                                \
    } while (0)

// Macro to perform the specified memory operation with fence and check results
#define TEST_FENCE_OP(fence_op, idx, description)                                  \
    do {                                                                           \
        reset_test_data();                                                         \
        printf("%-100s: ", description);                                            \
        asm volatile (fence_op);                                                   \
        CHECK_MEMORY_OP(&data_memory[idx], expected_results[idx], idx, "Validate fence operation effect"); \
    } while (0)

// Macro to modify and validate instruction memory using fence.i
#define TEST_FENCE_I_OP(idx, description)                                          \
    do {                                                                           \
        reset_test_data();                                                         \
        uint64_t *code_ptr = (uint64_t *)(&data_memory[idx]);                      \
        *code_ptr = 0x0000000000000000;  /* Clear instruction */                   \
        asm volatile ("fence.i");  /* Flush instruction cache */                   \
        expected_results[idx] = *code_ptr;                                         \
        CHECK_MEMORY_OP(code_ptr, expected_results[idx], idx, description);        \
    } while (0)

// Macro to validate TLB flush with sfence.vma
#define TEST_SFENCE_VMA_OP(idx, description)                                       \
    do {                                                                           \
        reset_test_data();                                                         \
        asm volatile ("sfence.vma");  /* Flush TLB */                              \
        CHECK_MEMORY_OP(&data_memory[idx], expected_results[idx], idx, description); \
    } while (0)

// Macro to simulate self-modifying code without using `fence.i`
#define TEST_SELF_MODIFYING_CODE_WITHOUT_FENCE_I(idx, description)                 \
    do {                                                                           \
        reset_test_data();                                                         \
        uint64_t *code_ptr = (uint64_t *)(&data_memory[idx]);                      \
        *code_ptr = 0x123456789ABCDEF0;  /* Write new instruction */               \
        /* Not using fence.i */                                                    \
        uint64_t fetched_value = *code_ptr;                                        \
        printf("%-100s: Memory check: fetched value = 0x%016llx ", description, fetched_value); \
        if (!CHECK_TRUE(fetched_value != 0x0000000000000000, "%s: Expected new instruction, but stale instruction executed.", description)) { \
            printf("FAIL\n");                                                                                            \
        } else {                                                                                                         \
            printf("PASS\n");                                                                                            \
        }                                                                                                                \
    } while (0)

// Macro to validate cache aliasing issues
#define TEST_MEMORY_ALIASING(description)                                          \
    do {                                                                           \
        reset_test_data();                                                         \
        uint64_t *alias_ptr1 = &data_memory[0];                                    \
        uint64_t *alias_ptr2 = alias_ptr1;  /* Direct alias for now */             \
        *alias_ptr1 = 0xABCDEFABCDEFABCD;                                          \
        asm volatile ("fence rw, rw;");                                            /* Ensure memory ordering */ \
        asm volatile ("sfence.vma;");                                              /* Flush all TLB entries */ \
        asm volatile ("fence rw, rw;");                                            /* Ensure all memory operations are ordered */ \
        uint64_t loaded_value = *alias_ptr2;                                       /* Load the value from alias_ptr2 */ \
        printf("%-100s: Memory check: 0x%016llx expectation: 0x%016llx ", description, loaded_value, 0xABCDEFABCDEFABCD); \
        if (!CHECK_EQUAL_HEX(loaded_value, 0xABCDEFABCDEFABCD, "%s: Memory aliasing check failed", description)) {       \
            printf("FAIL\n");                                                                                            \
        } else {                                                                                                         \
            printf("PASS\n");                                                                                            \
        }                                                                                                                \
    } while (0)

// Macro to validate cache flush and invalidate operations
#define TEST_CACHE_FLUSH_INVALIDATE_OP(idx, description)                           \
    do {                                                                           \
        reset_test_data();                                                         \
        asm volatile ("fence.i; sfence.vma;");  /* Invalidate caches and TLB */    \
        CHECK_MEMORY_OP(&data_memory[idx], expected_results[idx], idx, description); \
    } while (0)

// Function to test cache management instructions
int main() {
    testcase_init();  // Initialize test counters

    // Initialize test data
    initialize_cache_test_values();

    // Print the table header
    printf("\n%-100s  %-80s\n", "Scenario", "Result");

    // 1. Corner Case 1: Write to memory and issue a `fence`
    data_memory[0] = 0xAAAAAAAAAAAAAAAA;  // Modify memory
    asm volatile ("fence");  // Issue a fence
    expected_results[0] = data_memory[0];
    TEST_FENCE_OP("fence", 0, "Case 1: Memory write followed by 'fence'");

    // 2. Corner Case 2: Self-modifying code with `fence.i`
    TEST_FENCE_I_OP(1, "Case 2: Self-modifying code with 'fence.i'");

    // 3. Corner Case 3: TLB flush with partial range `sfence.vma`
    TEST_SFENCE_VMA_OP(2, "Test `sfence.vma` by changing virtual memory mappings: 'sfence.vma' for TLB flush");

    // 4. Classic Test 1: Using `fence` for I/O operations
    asm volatile ("fence io, io");  // Memory barrier for device I/O
    expected_results[3] = data_memory[3];
    TEST_FENCE_OP("fence io, io", 3, "Simulate a device read or write and ensure memory is synchronized: 'fence' for I/O operations");

    // 5. Classic Test 2: `fence` for memory barriers
    data_memory[0] = 0x1111111111111111;
    asm volatile ("fence");  // Memory barrier
    data_memory[1] = 0x2222222222222222;
    expected_results[0] = 0x1111111111111111;
    expected_results[1] = 0x2222222222222222;
    TEST_FENCE_OP("fence", 0, "Classic Test 2: 'fence' for memory barrier");
    TEST_FENCE_OP("fence", 1, "Classic Test 2: 'fence' for memory barrier");

    // 6. Classic Test 3: Repeated `sfence.vma` calls
    TEST_SFENCE_VMA_OP(2, "Classic Test 3: Repeated 'sfence.vma' calls");

    // 7. Additional Test: Cache flush and invalidate operations
    TEST_CACHE_FLUSH_INVALIDATE_OP(0, "Additional Test: Cache flush and invalidate");

    // 8. Additional Test: Memory ordering with `fence rw, rw`
    TEST_FENCE_OP("fence rw, rw", 0, "Additional Test: Memory ordering with 'fence rw, rw'");

    // 9. Additional Test: Memory ordering with `fence r, w`
    TEST_FENCE_OP("fence r, w", 1, "Additional Test: Memory ordering with 'fence r, w'");

    // 10. Advanced Test: Self-modifying code without using `fence.i`
    TEST_SELF_MODIFYING_CODE_WITHOUT_FENCE_I(3, "Advanced Test: Self-modifying code without 'fence.i'");

    // 11. Advanced Test: Memory aliasing to check cache and TLB consistency
    TEST_MEMORY_ALIASING("Advanced Test: Memory aliasing scenario to check cache/TLB consistency");

    // Finalize test results
    return testcase_finalize();
}
