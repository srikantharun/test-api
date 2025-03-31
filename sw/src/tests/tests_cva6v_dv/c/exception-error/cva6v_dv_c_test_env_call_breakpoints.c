// This is a test file for env_call_breakpoints
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test ECALL instruction
void test_ecall(uint64_t *regs) {
    // Set up registers with specific values
    regs[10] = 42; // a0 register

    // Use ECALL to trigger environment call
    __asm__ volatile (
        "li t0, 93\n"       // Load the ECALL code for RISC-V into t0
        "li a7, 0\n"        // Set a7 to 0 for the ECALL code
        "ecall\n"           // Make the environment call
    );

    // After ECALL, the value in a0 should remain unchanged
    printf("ECALL Test: a0 = %lu (expected 42)\n", regs[10]);
}

// Function to test EBREAK instruction
void test_ebreak(uint64_t *regs) {
    // Set up registers with specific values
    regs[10] = 99; // a0 register

    // Use EBREAK to trigger a breakpoint
    __asm__ volatile (
        "li t0, 1\n"        // Load the EBREAK code for RISC-V into t0
        "ebreak\n"          // Make the breakpoint call
    );

    // After EBREAK, the value in a0 should remain unchanged
    printf("EBREAK Test: a0 = %lu (expected 99)\n", regs[10]);
}

// Function to test environment call and breakpoints (ECALL, EBREAK)
void test_env_call_breakpoints() {
    uint64_t registers[32]; // Array to represent registers

    // Initialize registers
    initialize_registers();

    // Print starting message
    printf("Testing Environment Calls and Breakpoints...\n");

    // Test ECALL instruction
    test_ecall(registers);

    // Test EBREAK instruction
    test_ebreak(registers);

    // Print completion message
    printf("Environment Calls and Breakpoints Test Completed.\n");
}

int main() {
    printf("Running test: env_call_breakpoints\n");
    initialize_registers();
    test_env_call_breakpoints();
    return 0;
}
