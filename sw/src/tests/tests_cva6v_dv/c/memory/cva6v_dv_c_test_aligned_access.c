// This is a test file for aligned_access
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test aligned memory access operations
void test_aligned_access() {
    uint64_t memory[32]; // Memory array to perform aligned load/store operations
    uint64_t result; // Variable to store the result of the load operation

    // Initialize memory with known values
    for (int i = 0; i < 32; i++) {
        memory[i] = i * 0x1111111111111111; // Initialize each memory location with a unique pattern
    }

    // Perform aligned load and store operations
    for (int i = 0; i < 32; i++) {
        // Print before store operation
        printf("Storing to memory[%d]: 0x%llx\n", i, memory[i]);

        // Aligned Store Operation: Store the value of memory[i] into memory at index i
        __asm__ volatile (
            "sd %1, 0(%0)\n"
            :
            : "r"(&memory[i]), "r"(memory[i])
        );

        // Aligned Load Operation: Load the value from memory at index i into result
        __asm__ volatile (
            "ld %0, 0(%1)\n"
            : "=r"(result)
            : "r"(&memory[i])
        );

        // Print after load operation
        printf("Loaded from memory[%d]: 0x%llx\n", i, result);

        // Verify and print the results to verify correct load/store operation
        if (result != memory[i]) {
            printf("Aligned Access Test Failed at index %d: Expected 0x%llx, Got 0x%llx\n", i, memory[i], result);
            return;
        }
    }
    printf("Aligned Access Test Passed\n");
}

int main() {
    printf("Running test: aligned_access\n");
    initialize_registers();
    test_aligned_access();
    return 0;
}
