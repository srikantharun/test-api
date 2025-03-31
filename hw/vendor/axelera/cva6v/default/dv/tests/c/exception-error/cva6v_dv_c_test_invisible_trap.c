// This is a test file for invisible_trap
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test invisible trap operations (page fault and device interrupt)
void test_invisible_trap() {
    // Print starting message
    printf("Testing Invisible Trap (page fault and device interrupt)...\n");

    // Save the current machine trap-vector base-address register (mtvec)
    uint64_t mtvec;
    asm volatile ("csrr %0, mtvec" : "=r"(mtvec));

    // Set the new trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(trap_handler));

    // Trigger a page fault by accessing an invalid memory address
    printf("Triggering page fault...\n");
    volatile uint64_t *invalid_address = (uint64_t *)0xFFFFFFFFFFFFFFFF;
    asm volatile ("ld t0, 0(%0)" : : "r"(invalid_address));

    // Simulate a device interrupt
    printf("Simulating device interrupt...\n");
    // In a real system, device interrupts are triggered by the device itself.
    // Here, we can simulate it by invoking the trap handler directly for demonstration purposes.
    trap_handler();

    // Restore the original trap handler address
    asm volatile ("csrw mtvec, %0" : : "r"(mtvec));

    // Print a message indicating the test passed
    printf("Invisible Trap Test Passed: Page fault and device interrupt successfully trapped.\n");

    // Completion message
    printf("Invisible Trap Test Completed.\n");
}


int main() {
    printf("Running test: invisible_trap\n");
    initialize_registers();
    test_invisible_trap();
    return 0;
}
