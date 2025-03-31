// This is a test file for unaligned_access
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test unaligned memory access operations
void test_unaligned_access() {
    uint8_t memory[64]; // Memory array to perform unaligned load/store operations
    uint64_t result; // Variable to store the result of the load operation

    // Initialize memory with known values
    for (int i = 0; i < 64; i++) {
        memory[i] = i; // Initialize each memory location with its index value
    }

    // Perform unaligned load and store operations
    for (int i = 0; i < 57; i++) { // Loop until 57 to avoid out-of-bound access for 8-byte load
        // Unaligned Store Operation: Store 8 bytes from memory starting at index i
        uint64_t value = 0x1122334455667788; // Sample value to store
        __asm__ volatile (
            "sd %1, 0(%0)\n"
            :
            : "r"(&memory[i]), "r"(value)
        );

        // Unaligned Load Operation: Load 8 bytes from memory starting at index i into result
        __asm__ volatile (
            "ld %0, 0(%1)\n"
            : "=r"(result)
            : "r"(&memory[i])
        );

        // Print the results to verify correct load/store operation
        printf("Unaligned Access Test: Memory[%d to %d] = 0x%llx, Loaded Result = 0x%llx\n", i, i+7, value, result);
        if (result != value) {
            printf("Unaligned Access Test Failed at index %d: Expected 0x%llx, Got 0x%llx\n", i, value, result);
            return;
        }
    }
    printf("Unaligned Access Test Passed\n");
}


int main() {
    printf("Running test: unaligned_access\n");
    initialize_registers();
    test_unaligned_access();
    return 0;
}
