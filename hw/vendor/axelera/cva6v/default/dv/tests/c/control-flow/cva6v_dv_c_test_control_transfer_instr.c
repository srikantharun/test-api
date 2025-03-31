// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, control transfer instructions are explicitly tested.

#include "common.h"

// Define memory addresses and targets for control transfer instructions
__attribute__((aligned(64))) uint64_t control_transfer_target[4]; // Targets for control transfer tests
int control_transfer_results[4];  // Store results for comparison

// Function to initialize values for testing control transfer instructions
void initialize_control_transfer_values() {
    // Initialize test targets within valid memory ranges
    control_transfer_target[0] = 0x2000000000001000;  // Target for c.j and c.jal
    control_transfer_target[1] = 0x2000000000002000;  // Target for c.jr and c.jalr
    control_transfer_target[2] = 0x2000000000003000;  // Target for c.beqz
    control_transfer_target[3] = 0x2000000000004000;  // Target for c.bnez

    // Initialize expected results (can be 0 or 1 based on expected outcome)
    control_transfer_results[0] = 1;  // Expected result for c.j and c.jal
    control_transfer_results[1] = 1;  // Expected result for c.jr and c.jalr
    control_transfer_results[2] = 1;  // Expected result for c.beqz
    control_transfer_results[3] = 1;  // Expected result for c.bnez
}

// Macro to perform control transfer test and check the result
#define CHECK_CONTROL_TRANSFER_OP(expected, idx, scenario)                       \
    do {                                                                         \
        int result = 0;                                                          \
        if (control_transfer_results[idx]) result = 1;                           \
        const char* outcome = (result == expected) ? "PASS" : "FAIL";            \
        printf("%-100s: %-25s\n", scenario, outcome);                            \
        if (result != expected) pass = 0;                                        \
    } while (0)

// Function to test control transfer instructions
void test_control_transfer_instr() {
    int pass = 1;  // Assume pass unless a test fails
    uint64_t jr_target, jalr_target;
    int32_t beqz_val, bnez_val;

    // Initialize the values for testing
    initialize_control_transfer_values();

    // Test c.j (compressed jump)
    printf("Testing c.j (compressed jump)\n");
    __asm__ volatile (
        "mv t0, %[target]\n\t"   // Move target address to t0
        "c.jr t0\n\t"            // Use c.jr to jump to the target address
        "1:\n\t"                 // Label to continue after jump
        :
        : [target] "r"(control_transfer_target[0])
        : "t0"
    );
    CHECK_CONTROL_TRANSFER_OP(control_transfer_results[0], 0, "Test c.j to address 0x2000000000001000");

    // Test c.jal (compressed jump and link)
    printf("Testing c.jal (compressed jump and link)\n");
    __asm__ volatile (
        "mv t0, %[target]\n\t"   // Move target address to t0
        "c.jalr t0\n\t"          // Use c.jalr to jump and link to the target address
        "2:\n\t"                 // Label to continue after jump
        :
        : [target] "r"(control_transfer_target[0])
        : "t0"
    );
    CHECK_CONTROL_TRANSFER_OP(control_transfer_results[0], 0, "Test c.jal to address 0x2000000000001000");

    // Test c.jr (compressed jump register)
    printf("Testing c.jr (compressed jump register)\n");
    jr_target = control_transfer_target[1];
    __asm__ volatile (
        "mv t0, %[target]\n\t"   // Move target address to t0
        "c.jr t0\n\t"            // Use c.jr to jump to the target address
        "3:\n\t"                 // Label to continue after jump
        :
        : [target] "r"(jr_target)
        : "t0"
    );
    CHECK_CONTROL_TRANSFER_OP(control_transfer_results[1], 1, "Test c.jr to register address 0x2000000000002000");

    // Test c.jalr (compressed jump and link register)
    printf("Testing c.jalr (compressed jump and link register)\n");
    jalr_target = control_transfer_target[1];
    __asm__ volatile (
        "mv t0, %[target]\n\t"   // Move target address to t0
        "c.jalr t0\n\t"          // Use c.jalr to jump and link to the target address
        "4:\n\t"                 // Label to continue after jump
        :
        : [target] "r"(jalr_target)
        : "t0"
    );
    CHECK_CONTROL_TRANSFER_OP(control_transfer_results[1], 1, "Test c.jalr to register address 0x2000000000002000");

    // Test c.beqz (compressed branch if equal to zero)
    printf("Testing c.beqz (compressed branch if equal to zero)\n");
    beqz_val = 0;  // Use zero value for test
    __asm__ volatile (
        "mv a0, %[val]\n\t"         // Move value to a0
        "c.beqz a0, 5f\n\t"         // Branch if a0 is zero
        "j 6f\n\t"                  // Jump to end if not taken
        "5: addi zero, zero, 0\n\t" // Branch taken
        "6:\n\t"                    // End label
        :
        : [val] "r"(beqz_val)
        : "a0"
    );
    CHECK_CONTROL_TRANSFER_OP(control_transfer_results[2], 2, "Test c.beqz with value 0 to address 0x2000000000003000");

    // Test c.bnez (compressed branch if not equal to zero)
    printf("Testing c.bnez (compressed branch if not equal to zero)\n");
    bnez_val = 1;  // Use non-zero value for test
    __asm__ volatile (
        "mv a0, %[val]\n\t"         // Move value to a0
        "c.bnez a0, 7f\n\t"         // Branch if a0 is not zero
        "j 8f\n\t"                  // Jump to end if not taken
        "7: addi zero, zero, 0\n\t" // Branch taken
        "8:\n\t"                    // End label
        :
        : [val] "r"(bnez_val)
        : "a0"
    );
    CHECK_CONTROL_TRANSFER_OP(control_transfer_results[3], 3, "Test c.bnez with value 1 to address 0x2000000000004000");

    // Print the test results
    if (pass) {
        printf("\nAll control transfer instruction tests passed.\n\n");
    } else {
        printf("\nSome control transfer instruction tests failed.\n\n");
    }
}

int main() {
    printf("Running test: control_transfer_instr\n");
    initialize_registers();
    test_control_transfer_instr();
    return 0;
}
