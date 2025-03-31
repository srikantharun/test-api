// Unconditional Jump Tests: Author: Abhilash Chadhar
// This test file explicitly tests unconditional jump instructions in the RISC-V CVA6 processor.

#define PRINT_RESULT_JUMP(scenario, result) \
    printf("%-60s %-10s\n", scenario, result)

#include "common.h"

// Define the data block to be used in the stress test
__attribute__((aligned(64))) uint32_t data_block[2] = {0x0, 0x0};  // Aligned to 64 bytes per linker script

// Function to test unconditional jumps
void test_unconditional_jumps() {
    int pass = 1; // Assume pass unless a test fails

    // Test jump (`j`) to a known address
    asm volatile (
        ".align 4\n\t"                           // Ensure instruction alignment
        "j jump_label_1\n\t"                     // Jump to label
        "li t0, 0xdeadbeef\n\t"                  // Fail if executed
        ".align 4\n\t"                           // Align next instruction
        "jump_label_1:\n\t"
        "li t1, 0x12345678\n\t"                  // Expected execution
    );

    // Verify result of the first jump
    uint64_t jump_test1;
    asm volatile ("mv %0, t1" : "=r"(jump_test1));
    const char* result1 = (jump_test1 == 0x12345678) ? "PASS" : "FAIL";
    PRINT_RESULT_JUMP("Test unconditional jump to label (j)", result1);
    if (strcmp(result1, "FAIL") == 0) pass = 0;

    // Debug statement for first jump
    char jump_test1_str[50];
    uint64_to_str(jump_test1, jump_test1_str);
    // printf("Debug: Value in t1 after jump to label: %s\n", jump_test1_str);

    // Test jump and link (`jal`) with a return address
    uint64_t return_addr;
    asm volatile (
        ".align 4\n\t"                           // Ensure instruction alignment
        "auipc t0, 0\n\t"                        // Get the current PC
        "1: jal ra, jump_label_2\n\t"            // Jump and link
        "li t2, 0xdeadbeef\n\t"                  // Fail if executed
        ".align 4\n\t"                           // Align next instruction
        "jump_label_2:\n\t"
        "mv %0, ra\n\t"                          // Save return address
        : "=r"(return_addr)
    );

    // Calculate the expected address using assembly labels
    uint64_t current_pc;
    asm volatile (
        "la %0, 1b\n\t"                          // Get the address of label 1
        "addi %0, %0, 4\n\t"                     // The address after `jal`
        : "=r"(current_pc)
    );

    // Debug statements for `jal`
    char return_addr_str[50], current_pc_str[50];
    uint64_to_str(return_addr, return_addr_str);
    uint64_to_str(current_pc, current_pc_str);
    // printf("Debug: Return address in ra: %s\n", return_addr_str);
    // printf("Debug: Expected return address: %s\n", current_pc_str);

    // Verify the result of the jump and link
    const char* result2 = (return_addr == current_pc) ? "PASS" : "FAIL";
    PRINT_RESULT_JUMP("Test jump and link (jal) and return address", result2);
    if (strcmp(result2, "FAIL") == 0) pass = 0;

    // Test corner case: jumping to an aligned address
    asm volatile (
        ".align 4\n\t"                           // Align to 4-byte boundary
        "j jump_label_3\n\t"                     // Jump to the aligned label
        "li t3, 0xdeadbeef\n\t"                  // Fail if executed
        ".align 4\n\t"                           // Align next instruction
        "jump_label_3:\n\t"
        "li t4, 0x87654321\n\t"                  // Expected execution
    );

    // Verify result of the third jump
    uint64_t jump_test3;
    asm volatile ("mv %0, t4" : "=r"(jump_test3));
    const char* result3 = (jump_test3 == 0x87654321) ? "PASS" : "FAIL";
    PRINT_RESULT_JUMP("Test aligned unconditional jump (j)", result3);
    if (strcmp(result3, "FAIL") == 0) pass = 0;

    // Debug statement for third jump
    char jump_test3_str[50];
    uint64_to_str(jump_test3, jump_test3_str);
    // printf("Debug: Value in t4 after aligned jump: %s\n", jump_test3_str);

    // Final result check
    if (pass) {
        printf("All unconditional jump tests passed.\n");
    } else {
        printf("Some unconditional jump tests failed.\n");
    }
}

// Function for stress testing with load/store combinations and known buggy scenarios
void test_unconditional_jumps_stress() {
    int pass = 1; // Assume pass unless a test fails

    // Stress test: multiple jumps and memory access
    asm volatile (
        ".align 4\n\t"
        "la t0, data_block\n\t"                  // Load address of data block
        "j jump_label_stress_1\n\t"              // Unconditional jump
        "li t5, 0xdeadbeef\n\t"                  // Fail if executed
        ".align 4\n\t"
        "jump_label_stress_1:\n\t"
        "lw t1, 0(t0)\n\t"                       // Load data from memory
        "addi t1, t1, 1\n\t"                     // Increment loaded data
        "sw t1, 4(t0)\n\t"                       // Store back to memory
        "j jump_label_stress_2\n\t"              // Jump to another label
        "li t6, 0xdeadbeef\n\t"                  // Fail if executed
        ".align 4\n\t"
        "jump_label_stress_2:\n\t"
        "li x10, 0x12345678\n\t"                 // Use a general-purpose register
    );

    // Verify the stress test results
    uint64_t stress_test_result1;
    asm volatile ("mv %0, x10" : "=r"(stress_test_result1)); // Corrected to use general-purpose register x10
    const char* result_stress1 = (stress_test_result1 == 0x12345678) ? "PASS" : "FAIL";
    PRINT_RESULT_JUMP("Stress test: multiple jumps and memory access", result_stress1);
    if (strcmp(result_stress1, "FAIL") == 0) pass = 0;

    // Debug statement for stress test
    char stress_test_result1_str[50];
    uint64_to_str(stress_test_result1, stress_test_result1_str);
    // printf("Debug: Value in x10 after stress test: %s\n", stress_test_result1_str);

    // Known buggy scenario: jumping across memory boundaries
    asm volatile (
        ".align 4\n\t"
        "j jump_label_buggy_1\n\t"               // Jump to a new label
        "li x11, 0xdeadbeef\n\t"                 // Use a general-purpose register
        ".align 4\n\t"
        "jump_label_buggy_1:\n\t"
        "li x12, 0x87654321\n\t"                 // Use a general-purpose register
    );

    // Verify result of the buggy scenario
    uint64_t buggy_scenario_result;
    asm volatile ("mv %0, x12" : "=r"(buggy_scenario_result)); // Corrected to use general-purpose register x12
    const char* result_buggy = (buggy_scenario_result == 0x87654321) ? "PASS" : "FAIL";
    PRINT_RESULT_JUMP("Known buggy scenario: jump across memory boundaries", result_buggy);
    if (strcmp(result_buggy, "FAIL") == 0) pass = 0;

    // Debug statement for buggy scenario
    char buggy_scenario_result_str[50];
    uint64_to_str(buggy_scenario_result, buggy_scenario_result_str);
    // printf("Debug: Value in x12 after buggy scenario: %s\n", buggy_scenario_result_str);

    // Final result check for stress tests
    if (pass) {
        printf("All stress tests passed.\n");
    } else {
        printf("Some stress tests failed.\n");
    }
}

int main() {
    // Print the header for the test results
    printf("\n%-60s %-25s \n", "Scenario", "Result");

    // Execute unconditional jump tests
    test_unconditional_jumps();

    // Execute stress tests for unconditional jumps
    test_unconditional_jumps_stress();

    return 0;
}
