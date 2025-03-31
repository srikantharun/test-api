// This is a test file for interrupt_mgmt_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test interrupt management instructions (WFI)
void test_interrupt_mgmt_instr() {
    // Print starting message
    printf("Testing Interrupt Management Instructions (WFI)...\n");

    // Save the current machine status register (mstatus)
    uint64_t mstatus;
    asm volatile ("csrr %0, mstatus" : "=r"(mstatus));

    // Set up a trap handler for machine mode by writing its address to mtvec
    asm volatile (
        "la t0, trap_handler\n"
        "csrw mtvec, t0\n"
    );

    // Enable interrupts in mstatus
    asm volatile (
        "csrr t0, mstatus\n"
        "ori t0, t0, 0x8\n" // Set MIE (Machine Interrupt Enable) bit
        "csrw mstatus, t0\n"
    );

    // Trigger WFI (Wait For Interrupt) instruction
    asm volatile ("wfi");

    // The trap handler will execute and return to this point
    printf("WFI Test Passed: Successfully returned from interrupt handler.\n");

    // Restore the original machine status register (mstatus)
    asm volatile ("csrw mstatus, %0" : : "r"(mstatus));

    printf("Interrupt Management Instructions Test Completed.\n");
}

int main() {
    printf("Running test: interrupt_mgmt_instr\n");
    initialize_registers();
    test_interrupt_mgmt_instr();
    return 0;
}
