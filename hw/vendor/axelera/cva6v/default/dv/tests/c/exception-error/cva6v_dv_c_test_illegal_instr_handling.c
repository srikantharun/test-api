// This is a test file for illegal_instr_handling
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


//todo - need to add the full list with arch and spec consultation
// Function to test handling of illegal instructions
void test_illegal_instr_handling() {
    uint64_t result;

    // Test illegal instruction handling
    printf("Testing Illegal Instruction Handling...\n");
    asm volatile (" .word 0xFFFFFFFF ");  // Illegal instruction
    printf("Illegal Instruction Handling Test: Expected to trigger an illegal instruction exception.\n");

    // Test invalid CSR access - should trigger an illegal instruction exception
    printf("Testing Invalid CSR Access Handling...\n");
    asm volatile ("csrrw %0, 0xFFF, %1" : "=r"(result) : "r"(0));  // Invalid CSR address
    printf("Invalid CSR Access Handling Test: Expected to trigger an illegal instruction exception.\n");

    printf("Illegal Instruction Handling Tests Completed.\n");
}

int main() {
    printf("Running test: illegal_instr_handling\n");
    test_illegal_instr_handling();
    return 0;
}
