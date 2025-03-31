// This is a test file for mem_order_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to perform a series of memory writes and reads to test FENCE instruction
void test_fence(uint64_t *regs, uint64_t *memory) {
    uint64_t result;

    // Write to memory without any fence instruction
    memory[0] = regs[1];
    memory[1] = regs[2];

    // Read from memory without any fence instruction
    result = memory[0] + memory[1];
    printf("Without FENCE: memory[0] + memory[1] = %lu\n", result);

    // Write to memory and use fence instruction to ensure ordering
    memory[2] = regs[3];
    __asm__ volatile ("fence"); // FENCE ensures all prior memory operations are completed before any subsequent ones

    memory[3] = regs[4];
    __asm__ volatile ("fence"); // Another FENCE to ensure all prior memory operations are completed

    // Read from memory after fence instruction
    result = memory[2] + memory[3];
    printf("With FENCE: memory[2] + memory[3] = %lu\n", result);
}

// Function to test FENCE.I instruction which orders instruction fetches
void test_fence_i(uint64_t *regs, uint64_t *memory) {
    uint64_t result;

    // Write to memory
    memory[4] = regs[5];

    // Use FENCE.I to ensure instruction fetch ordering
    __asm__ volatile ("fence.i"); // FENCE.I ensures all prior memory operations are visible to instruction fetches

    // Read from memory after fence.i instruction
    result = memory[4];
    printf("With FENCE.I: memory[4] = %lu\n", result);
}

// Function to test memory ordering instructions (FENCE, FENCE.I)
void test_mem_order_instr() {
    uint64_t registers[32]; // Array to represent registers
    uint64_t memory[32];    // Array to represent memory

    // Initialize registers and memory
    initialize_registers();
    for (int i = 0; i < 32; i++) {
        memory[i] = 0; // Initialize memory to zero
    }

    // Print starting message
    printf("Testing Memory Ordering Instructions...\n");

    // Test FENCE instruction
    test_fence(registers, memory);

    // Test FENCE.I instruction
    test_fence_i(registers, memory);

    // Print completion message
    printf("Memory Ordering Instructions Test Completed.\n");
}

int main() {
    printf("Running test: mem_order_instr\n");
    initialize_registers();
    test_mem_order_instr();
    return 0;
}
