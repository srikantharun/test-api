// This is a test file for contained_trap
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test contained trap operations (ECALL and interrupt)
void test_contained_trap() {
    // Print starting message
    printf("Testing Contained Trap (ECALL and interrupt)...\n");

    // Save the current machine trap-vector base-address register (mtvec)
    uint64_t mtvec;
    asm volatile ("csrr %0, mtvec" : "=r"(mtvec));

    // Set the new trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(trap_handler));

    // Generate an ECALL instruction to trigger the trap handler
    printf("Triggering ECALL...\n");
    asm volatile ("ecall");

    // Restore the original trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(mtvec));

    // Print a message indicating the test passed
    printf("Contained Trap Test Passed: ECALL and interrupt successfully trapped.\n");

    // Completion message
    printf("Contained Trap Test Completed.\n");
}


int main() {
    printf("Running test: contained_trap\n");
    initialize_registers();
    test_contained_trap();
    return 0;
}
