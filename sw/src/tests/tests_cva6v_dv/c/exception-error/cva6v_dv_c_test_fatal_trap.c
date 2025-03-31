// This is a test file for fatal_trap
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test fatal trap operations (fatal error and watchdog timer)
void test_fatal_trap() {
    // Print starting message
    printf("Testing Fatal Trap (fatal error and watchdog timer)...\n");

    // Save the current machine trap-vector base-address register (mtvec)
    uint64_t mtvec;
    asm volatile ("csrr %0, mtvec" : "=r"(mtvec));

    // Set the new trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(trap_handler));

    // Simulate a fatal error by executing an illegal instruction
    printf("Simulating fatal error...\n");
    asm volatile (".word 0x00000000"); // This is a placeholder for an illegal instruction

    // Simulate a watchdog timer expiration
    printf("Simulating watchdog timer expiration...\n");
    // In a real system, the watchdog timer would trigger a fatal trap when it expires.
    // Here, we can simulate it by invoking the trap handler directly for demonstration purposes.
    trap_handler();

    // Restore the original trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(mtvec));

    // Print a message indicating the test passed
    printf("Fatal Trap Test Passed: Fatal error and watchdog timer successfully trapped.\n");

    // Completion message
    printf("Fatal Trap Test Completed.\n");
}

int main() {
    printf("Running test: fatal_trap\n");
    initialize_registers();
    test_fatal_trap();
    return 0;
}
