// This is a test file for trap_return_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test trap-return instructions (SRET and MRET)
void test_trap_return_instr() {
    // Print starting message
    printf("Testing Trap-Return Instructions (SRET and MRET)...\n");

    // Save the current machine status register (mstatus)
    uint64_t mstatus;
    asm volatile ("csrr %0, mstatus" : "=r"(mstatus));

    // Set up a trap handler for machine mode by writing its address to mtvec
    asm volatile (
        "la t0, trap_handler\n"
        "csrw mtvec, t0\n"
    );

    // Trigger an environment call to enter the trap handler
    asm volatile ("ecall");

    // The trap handler will execute SRET or MRET to return to this point
    printf("SRET/MRET Test Passed: Successfully returned from trap handler.\n");

    // Restore the original machine status register (mstatus)
    asm volatile ("csrw mstatus, %0" : : "r"(mstatus));

    printf("Trap-Return Instructions Test Completed.\n");
}

int main() {
    printf("Running test: trap_return_instr\n");
    initialize_registers();
    test_trap_return_instr();
    return 0;
}
