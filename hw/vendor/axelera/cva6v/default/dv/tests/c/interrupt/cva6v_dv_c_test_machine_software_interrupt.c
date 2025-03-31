// Test file for Machine Software Interrupt (MSI)
// CVA6V directed C tests: Author Abhilash Chadhar
// In this test, we verify the correct handling of MSI by enabling, triggering, and clearing the MSI.

#include "common.h"


// Trap handler to handle Machine Software Interrupt (MSI)
void rtrap_handler(void) {
    uint64_t mcause, mepc, mstatus, mip;

    // Read mcause, mepc, mstatus, and mip to check the cause of the trap and interrupt status
    asm volatile("csrr %0, mcause" : "=r"(mcause));
    asm volatile("csrr %0, mepc" : "=r"(mepc));
    asm volatile("csrr %0, mstatus" : "=r"(mstatus));
    asm volatile("csrr %0, mip" : "=r"(mip));

    // Print out the values of relevant registers for debugging
    printf("Trap Handler Triggered:\n");
    printf("mcause: 0x%lx\n", mcause);
    printf("mepc: 0x%lx\n", mepc);
    printf("mstatus: 0x%lx\n", mstatus);
    printf("mip: 0x%lx\n", mip);

    // Check if the trap was caused by MSI
    if ((mcause & 0xFFF) == 3) { // 3 indicates MSI in machine mode
        printf("MSI triggered and handled!\n");
        interrupt_handled = 1;

        // Clear the software interrupt by clearing the MSIP bit in mip
        asm volatile("csrc mip, %0" :: "r"(0x8)); // Clear MSIP bit in mip

        // Increment the program counter to avoid re-triggering the same instruction
        asm volatile("csrw mepc, %0" :: "r"(mepc + 4));
    } else {
        printf("MSI not triggered! mcause indicates different interrupt or exception.\n");
        printf("FAIL: Unexpected cause value: 0x%lx\n", mcause);
    }
}

// Function to trigger the MSI
void trigger_msi(void) {
    //printf("Triggering MSI by setting MSIP bit...\n");
    // Set the MSIP bit in mip to trigger the interrupt
    asm volatile("csrs mip, %0" :: "r"(0x8)); // Set MSIP bit in mip
}

// Function to enable MSI in mie
void enable_msi(void) {
    //printf("Enabling MSI...\n");
    asm volatile("csrs mie, %0" :: "r"(0x8)); // Enable MSI in mie
}

// Function to disable MSI in mie
void disable_msi(void) {
    //printf("Disabling MSI...\n");
    asm volatile("csrc mie, %0" :: "r"(0x8)); // Disable MSI in mie
}

// Function to initialize the test environment
void setup_msi_test(void) {
    //printf("Setting up MSI test environment...\n");

    // Set the trap vector to the trap handler function
    asm volatile("csrw mtvec, %0" :: "r"(trap_handler));

    // Enable interrupts globally by setting the MIE bit in mstatus
    asm volatile("csrs mstatus, %0" :: "r"(0x8)); // Set MIE in mstatus
}

int main(void) {
    //printf("Starting MSI Test...\n");

    // Step 1: Setup the MSI environment
    setup_msi_test();

    // Step 2: Enable MSI
    enable_msi();

    // Step 3: Trigger the MSI
    trigger_msi();

    // Wait to ensure the interrupt is handled
    for (volatile int i = 0; i < 100000; i++);

    // Step 4: Check if the interrupt was handled correctly
    if (interrupt_handled) {
        printf("\nMSI Test Passed: Interrupt was handled successfully.\n");
    } else {
        printf("\nMSI Test Failed: Interrupt was not handled.\n");
    }

    // Step 5: Disable MSI after the test
    disable_msi();

    return 0;
}
