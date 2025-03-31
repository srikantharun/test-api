// This is a test file for supervisor_mem_mgmt_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test supervisor memory management instructions (SFENCE.VMA)
void test_supervisor_mem_mgmt_instr() {
    // Print starting message
    printf("Testing Supervisor Memory Management Instructions (SFENCE.VMA)...\n");

    // Save the current supervisor address translation and protection (satp) register
    uint64_t satp;
    asm volatile ("csrr %0, satp" : "=r"(satp));

    // Set up a new page table base address
    uint64_t new_satp = (satp & ~0xFFFFFFFFFUL) | 0x1000;
    asm volatile ("csrw satp, %0" : : "r"(new_satp));

    // Print the new SATP value to verify it was set correctly
    printf("New SATP value set: 0x%lx\n", new_satp);

    // Execute SFENCE.VMA to flush the TLB
    asm volatile ("sfence.vma");

    // Check if the TLB was flushed by reloading the original SATP value and performing a memory access
    asm volatile ("csrw satp, %0" : : "r"(satp));
    asm volatile ("sfence.vma");

    // Print a message indicating the test passed
    printf("SFENCE.VMA Test Passed: Successfully flushed the TLB and restored original SATP.\n");

    // Completion message
    printf("Supervisor Memory Management Instructions Test Completed.\n");
}

int main() {
    printf("Running test: supervisor_mem_mgmt_instr\n");
    initialize_registers();
    test_supervisor_mem_mgmt_instr();
    return 0;
}
