// This is a test file for single_interrupts
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

volatile int interrupt_occurred = 0; // Flag to indicate if an interrupt has occurred

// ISR (Interrupt Service Routine) to handle the interrupt
void isr() {
    interrupt_occurred = 1; // Set the flag to indicate interrupt handling
    printf("Interrupt occurred and handled.\n"); // Print that interrupt is handled
}

// Function to simulate a single interrupt and test its handling
void test_single_interrupts() {

    // Simulate enabling interrupts and triggering an interrupt
    __asm__ volatile ("csrsi mstatus, 8"); // Enable machine interrupts
    __asm__ volatile ("csrsi mie, 8"); // Enable external interrupts

    // Simulate the occurrence of an interrupt
    __asm__ volatile ("ecall"); // Environment call to trigger an interrupt

    // Check if the interrupt was handled
    if (interrupt_occurred) {
        printf("Single interrupt test passed.\n"); // Print success message
    } else {
        printf("Single interrupt test failed.\n"); // Print failure message
    }

    // Disable interrupts after the test
    __asm__ volatile ("csrci mie, 8"); // Disable external interrupts
    __asm__ volatile ("csrci mstatus, 8"); // Disable machine interrupts
}

int main() {
    printf("Running test: single_interrupts\n");
    initialize_registers();
    test_single_interrupts();
    return 0;
}
