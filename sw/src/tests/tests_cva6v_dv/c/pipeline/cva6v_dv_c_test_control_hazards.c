// This is a test file for control_hazards
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test control hazards in the pipeline
void test_control_hazards() {
    uint64_t pc_before = 0, pc_after = 0; // Initialize variables to store program counter values
    uint64_t x1 = 10, x2 = 20; // Initialize registers with test values

    // Assign random values to x1 and x2
    x1 = rand();
    x2 = rand();
    printf("Random values: x1 = %ld, x2 = %ld\n", x1, x2);

    // Branch Prediction
    // This test ensures that the branch prediction mechanism in the pipeline works correctly.
    __asm__ volatile (
        "auipc %0, 0\n"          // Get current PC value into pc_before
        "beq %2, %3, 1f\n"      // Branch if x1 == x2 (unlikely branch)
        "addi %1, %1, 1\n"      // Increment x1 to ensure branch is not taken
        "1: auipc %0, 0\n"      // Get new PC value into pc_after
        : "=r"(pc_before), "=r"(x1), "=r"(pc_after)
        : "r"(x2)
    );
    printf("Branch Prediction Test: PC before = %ld, PC after = %ld\n", pc_before, pc_after);

    // Pipeline Flushes
    // This test ensures that the pipeline correctly flushes instructions when a branch is taken.
    __asm__ volatile (
        "auipc %0, 0\n"          // Get current PC value into pc_before
        "bne %2, %3, 1f\n"      // Branch if x1 != x2 (expected branch)
        "addi %1, %1, 1\n"      // Increment x1 (should be flushed if branch is taken)
        "1: auipc %0, 0\n"      // Get new PC value into pc_after
        : "=r"(pc_before), "=r"(x1), "=r"(pc_after)
        : "r"(x2)
    );
    printf("Pipeline Flush Test: PC before = %ld, PC after = %ld\n", pc_before, pc_after);

    // Ensuring branch is taken correctly and no unwanted instructions are executed
    if (pc_before == pc_after) {
        printf("Pipeline Flush Test Failed\n");
    } else {
        printf("Pipeline Flush Test Passed\n");
    }
}

int main() {
    printf("Running test: control_hazards\n");
    initialize_registers();
    test_control_hazards();
    return 0;
}
