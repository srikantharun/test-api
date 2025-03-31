// This is a test file for nested_interrupts
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

//TODO: incomplete test - need more understandin gof ISRs

// Global flag to indicate if the first interrupt occurred
volatile int first_interrupt_occurred = 0;
// Global flag to indicate if the second interrupt occurred
volatile int second_interrupt_occurred = 0;

// First ISR (Interrupt Service Routine) to handle the first interrupt
void first_isr() {
    first_interrupt_occurred = 1; // Set the flag to indicate the first interrupt handling
    printf("First interrupt occurred and handled.\n"); // Print that the first interrupt is handled

    // Trigger the second interrupt within the first ISR
    __asm__ volatile ("csrsi mie, 8"); // Enable external interrupts for the nested interrupt
    __asm__ volatile ("ecall"); // Environment call to trigger the second interrupt
}

// Second ISR (Interrupt Service Routine) to handle the second interrupt
void second_isr() {
    second_interrupt_occurred = 1; // Set the flag to indicate the second interrupt handling
    printf("Second interrupt occurred and handled.\n"); // Print that the second interrupt is handled
}

// Function to simulate nested interrupts and test their handling
void test_nested_interrupts() {
    // Initialize the flags
    first_interrupt_occurred = 0;
    second_interrupt_occurred = 0;

    // Enable machine interrupts
    __asm__ volatile ("csrsi mstatus, 8");
    // Enable external interrupts
    __asm__ volatile ("csrsi mie, 8");

    // Simulate the occurrence of the first interrupt
    __asm__ volatile ("ecall");

    // Check if both interrupts were handled
    if (first_interrupt_occurred && second_interrupt_occurred) {
        printf("Nested interrupt test passed.\n"); // Print success message
    } else {
        printf("Nested interrupt test failed.\n"); // Print failure message
    }

    // Disable interrupts after the test
    __asm__ volatile ("csrci mie, 8"); // Disable external interrupts
    __asm__ volatile ("csrci mstatus, 8"); // Disable machine interrupts
}

int main() {
    printf("Running test: nested_interrupts\n");
    initialize_registers();
    test_nested_interrupts();
    return 0;
}
