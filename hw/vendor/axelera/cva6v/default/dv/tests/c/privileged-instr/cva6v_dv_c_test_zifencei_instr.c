// This is a test file for zifencei_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test the FENCE.I instruction
// FENCE.I instruction is used to synchronize the instruction and data streams by ensuring that all previous stores
// are visible to instruction fetches that occur after the FENCE.I instruction.
void test_zifencei_instr() {
    // Print starting message
    printf("Testing Zifencei Instruction...\n");

    // Initialize registers
    uint64_t data = 0xDEADBEEF, result;

    // Perform a store operation
    // Storing the value 0xDEADBEEF to memory location pointed by a0
    __asm__ volatile (
        "sw %1, 0(%0)\n"
        :
        : "r"(&data), "r"(data)
    );

    // Execute FENCE.I instruction
    // This instruction ensures all previous memory writes are completed before any further instruction fetches
    __asm__ volatile (
        "fence.i\n"
    );

    // Perform a load operation
    // Loading the value from memory location pointed by a0 to a register
    __asm__ volatile (
        "lw %0, 0(%1)\n"
        : "=r"(result)
        : "r"(&data)
    );

    // Print the result and check if it matches the expected value
    printf("FENCE.I: Data=0x%lx Result=0x%lx %s\n", data, result, (result == data) ? "PASS" : "FAIL");

    // Completion message
    printf("Zifencei Instruction Test Completed.\n");
}

int main() {
    printf("Running test: zifencei_instr\n");
    initialize_registers();
    test_zifencei_instr();
    return 0;
}
