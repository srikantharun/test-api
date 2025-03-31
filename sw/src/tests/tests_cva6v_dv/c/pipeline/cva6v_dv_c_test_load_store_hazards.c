#include "common.h"
#include "testutils.h"

#define NUM_TESTS 8 // Number of tests for load/store order hazards

// Corrected expected results for different load/store order hazard tests
uint32_t expected_results[NUM_TESTS] = {
    0x2000, 0x3000, 0x4000, 0x7000, 0x6000, 0xB000, 0x6000, 0xD000
};

// Memory to store the results
uint32_t results[NUM_TESTS];

// Define addresses to use within the cacheable memory region
volatile uint32_t *mem_address_0 = (volatile uint32_t *)0x2000000040; // Aligned to 64 bytes
volatile uint32_t *mem_address_1 = (volatile uint32_t *)0x2000000080; // Aligned to 64 bytes

// Inline assembly function to test load/store order hazards
void test_load_store_order_hazards() {
    // Store-Store-Load Pattern
    __asm__ volatile (
        "li t0, 0x1000;"              // Load immediate value 0x1000 into t0
        "sw t0, 0(%[addr0]);"         // Store t0 at memory address pointed by addr0
        "li t0, 0x2000;"              // Load new immediate value 0x2000 into t0
        "sw t0, 0(%[addr0]);"         // Store new value at the same address
        "lw t2, 0(%[addr0]);"         // Load value back from memory into t2
        "sw t2, %0;"                  // Store result to results[0]
        : "=m"(results[0])
        : [addr0] "r"(mem_address_0)
    );

    // Store-Load-Store Pattern
    __asm__ volatile (
        "li t0, 0x3000;"              // Load immediate value 0x3000 into t0
        "sw t0, 0(%[addr1]);"         // Store t0 at memory address pointed by addr1
        "lw t2, 0(%[addr1]);"         // Load the value back into t2
        "li t0, 0x4000;"              // Load new immediate value 0x4000 into t0
        "sw t0, 0(%[addr1]);"         // Store the new value at the same address
        "sw t2, %0;"                  // Store the loaded result to results[1]
        : "=m"(results[1])
        : [addr1] "r"(mem_address_1)
    );

    // Load-Store-Load Pattern
    __asm__ volatile (
        "li t0, 0x4000;"              // Load immediate value 0x4000 into t0
        "sw t0, 0(%[addr0]);"         // Store t0 at memory address pointed by addr0
        "lw t1, 0(%[addr0]);"         // Load from memory at the address in addr0
        "sw t1, %0;"                  // Store result to results[2]
        : "=m"(results[2])
        : [addr0] "r"(mem_address_0)
    );

    // Store-Load-Store Pattern with Rewrites
    __asm__ volatile (
        "li t0, 0x5000;"              // Load immediate value 0x5000 into t0
        "sw t0, 0(%[addr1]);"         // Store t0 at memory address pointed by addr1
        "li t0, 0x7000;"              // Load new immediate value 0x7000 into t0
        "sw t0, 0(%[addr1]);"         // Store new value at the same address
        "lw t2, 0(%[addr1]);"         // Load value back from memory into t2
        "sw t2, %0;"                  // Store result to results[3]
        : "=m"(results[3])
        : [addr1] "r"(mem_address_1)
    );

    // Store-Load Pattern
    __asm__ volatile (
        "li t0, 0x6000;"              // Load immediate value 0x6000 into t0
        "sw t0, 0(%[addr0]);"         // Store t0 at memory address pointed by addr0
        "lw t2, 0(%[addr0]);"         // Load value back from memory into t2
        "sw t2, %0;"                  // Store result to results[4]
        : "=m"(results[4])
        : [addr0] "r"(mem_address_0)
    );

    // Store-Store-Store Pattern
    __asm__ volatile (
        "li t0, 0x7000;"              // Load immediate value 0x7000 into t0
        "sw t0, 0(%[addr1]);"         // Store t0 at memory address pointed by addr1
        "li t0, 0xA000;"              // Load new immediate value 0xA000 into t0
        "sw t0, 0(%[addr1]);"         // Store new value at the same address
        "li t0, 0xB000;"              // Load another new immediate value 0xB000 into t0
        "sw t0, 0(%[addr1]);"         // Store another new value at the same address
        "lw t2, 0(%[addr1]);"         // Load value back from memory into t2
        "sw t2, %0;"                  // Store result to results[5]
        : "=m"(results[5])
        : [addr1] "r"(mem_address_1)
    );

    // Load-Store Pattern
    __asm__ volatile (
        "li t0, 0x6000;"              // Correct value to be loaded into memory for this test
        "sw t0, 0(%[addr0]);"         // Store 0x6000 into memory location
        "lw t1, 0(%[addr0]);"         // Load from memory at the address in addr0
        "sw t1, 0(%[addr0]);"         // Store value from t1 back to the same address
        "lw t2, 0(%[addr0]);"         // Load back from memory into t2
        "sw t2, %0;"                  // Store result to results[6]
        : "=m"(results[6])
        : [addr0] "r"(mem_address_0)
    );

    // Store-Load-Store-Load Pattern
    __asm__ volatile (
        "li t0, 0x8000;"              // Load immediate value 0x8000 into t0
        "sw t0, 0(%[addr1]);"         // Store t0 at memory address pointed by addr1
        "lw t1, 0(%[addr1]);"         // Load value back from memory into t1
        "li t0, 0xD000;"              // Load new immediate value 0xD000 into t0
        "sw t0, 0(%[addr1]);"         // Store new value at the same address
        "lw t2, 0(%[addr1]);"         // Load the latest value back into t2
        "sw t2, %0;"                  // Store result to results[7]
        : "=m"(results[7])
        : [addr1] "r"(mem_address_1)
    );
}

int main() {
    testcase_init();  // Initialize test case

    test_load_store_order_hazards();

    // Check results using testutils functions
    for (int i = 0; i < NUM_TESTS; i++) {
        // Print detailed descriptions for each test scenario
        switch (i) {
            case 0:
                printf("Test 0: Store-Store-Load Pattern\n");
                printf("Description: Ensures the second store overwrites the first, and the loaded value matches the latest store.\n");
                break;
            case 1:
                printf("Test 1: Store-Load-Store Pattern\n");
                printf("Description: Verifies that a load between stores fetches the correct value before being overwritten by the next store.\n");
                break;
            case 2:
                printf("Test 2: Load-Store-Load Pattern\n");
                printf("Description: Checks consistency by verifying that the store updates the memory correctly after a load, and subsequent loads fetch the updated value.\n");
                break;
            case 3:
                printf("Test 3: Store-Load-Store Pattern with Rewrites\n");
                printf("Description: Confirms that after a store, load, and another store, the memory holds the final stored value.\n");
                break;
            case 4:
                printf("Test 4: Store-Load Pattern\n");
                printf("Description: Validates that a value stored in memory is immediately available for loading without intermediate operations.\n");
                break;
            case 5:
                printf("Test 5: Store-Store-Store Pattern\n");
                printf("Description: Ensures multiple sequential stores correctly update the memory to the last stored value.\n");
                break;
            case 6:
                printf("Test 6: Load-Store Pattern\n");
                printf("Description: Tests the load-followed-by-store sequence to confirm data consistency in memory operations.\n");
                break;
            case 7:
                printf("Test 7: Store-Load-Store-Load Pattern\n");
                printf("Description: Ensures that intermediate loads between stores do not affect the final stored result in memory.\n");
                break;
        }

        // Print the expected and actual results
        printf("Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
        CHECK_EQUAL_INT(expected_results[i], results[i], "Test %d: Expected 0x%x, Got 0x%x", i, expected_results[i], results[i]);
    }

    return testcase_finalize();  // Finalize test case and return result
}
