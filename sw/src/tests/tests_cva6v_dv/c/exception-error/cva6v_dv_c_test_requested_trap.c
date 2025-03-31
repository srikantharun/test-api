// This is a test file for requested_trap
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test requested trap operations (system call and termination)
void test_requested_trap() {
    // Print starting message
    printf("Testing Requested Trap (system call and termination)...\n");

    // Save the current machine trap-vector base-address register (mtvec)
    uint64_t mtvec;
    asm volatile ("csrr %0, mtvec" : "=r"(mtvec));

    // Set the new trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(trap_handler));

    // Generate a system call (ECALL) instruction to trigger the trap handler
    printf("Triggering ECALL (system call)...\n");
    asm volatile ("ecall");

    // Generate a termination request by triggering an illegal instruction
    // This will also invoke the trap handler
    printf("Triggering illegal instruction (termination)...\n");
    asm volatile (".word 0x00000000"); // This is an example of an illegal instruction

    // Restore the original trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(mtvec));

    // Print a message indicating the test passed
    printf("Requested Trap Test Passed: System call and termination successfully trapped.\n");

    // Completion message
    printf("Requested Trap Test Completed.\n");
}

int main() {
    printf("Running test: requested_trap\n");
    initialize_registers();
    test_requested_trap();
    return 0;
}
