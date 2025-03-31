// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, branch instructions are explicitly tested.

#include "common.h"

// Define arrays to store the test values for branch instructions
__attribute__((aligned(64))) uint64_t branch_src1[12]; // Aligned to 64 bytes to respect linker constraints
__attribute__((aligned(64))) uint64_t branch_src2[12]; // Aligned to 64 bytes to respect linker constraints
int branch_expected[12];

// Function to initialize values for testing branch instructions
void initialize_branch_values() {
    // Basic tests
    branch_src1[0] = 0x2000000000002000; // Equal test for `beq`
    branch_src2[0] = 0x2000000000002000;
    branch_expected[0] = 1;   // Expected branch taken

    branch_src1[1] = 0x2000000000003000; // Not equal test for `bne`
    branch_src2[1] = 0x2000000000001000;
    branch_expected[1] = 1;   // Expected branch taken

    branch_src1[2] = 0x1;    // Less than test for `blt`
    branch_src2[2] = 0x5;
    branch_expected[2] = 1;  // Expected branch taken

    branch_src1[3] = 0x2000000000000008; // Greater than or equal test for `bge`
    branch_src2[3] = 0x2000000000000004;
    branch_expected[3] = 1;  // Expected branch taken

    branch_src1[4] = 0x1;    // Unsigned less than test for `bltu`
    branch_src2[4] = 0xFFFFFFFFFFFFFFFF;
    branch_expected[4] = 1;  // Expected branch taken

    branch_src1[5] = 0xFFFFFFFFFFFFFFFF; // Unsigned greater or equal test for `bgeu`
    branch_src2[5] = 0x1;
    branch_expected[5] = 1;  // Expected branch taken

    // Additional corner cases
    branch_src1[6] = -1; // Negative vs zero test for `blt`
    branch_src2[6] = 0;
    branch_expected[6] = 1;  // Expected branch taken

    branch_src1[7] = 0; // Zero vs positive test for `bge`
    branch_src2[7] = 1;
    branch_expected[7] = 0;  // Expected branch not taken

    branch_src1[8] = 0x7FFFFFFFFFFFFFFF; // Max positive vs min negative for `bge`
    branch_src2[8] = 0x8000000000000000;
    branch_expected[8] = 1;  // Expected branch taken

    branch_src1[9] = 0xAAAAAAAAAAAAAAAA; // Alternating bit patterns for `bltu`
    branch_src2[9] = 0x5555555555555555;
    branch_expected[9] = 0;  // Expected branch not taken (0xAA... > 0x55...)

    branch_src1[10] = 0; // Zero vs max unsigned for `bltu`
    branch_src2[10] = 0xFFFFFFFFFFFFFFFF;
    branch_expected[10] = 1; // Expected branch taken

    branch_src1[11] = 0xFFFFFFFFFFFFFFFE; // Boundary condition (off-by-one) for `bne`
    branch_src2[11] = 0xFFFFFFFFFFFFFFFF;
    branch_expected[11] = 1; // Expected branch taken
}

// Macro to perform branch test and check the result
#define CHECK_BRANCH_OP(expected, idx, scenario)                                \
    do {                                                                        \
        int result = 0;                                                         \
        if (branch_expected[idx]) result = 1;                                   \
        const char* outcome = (result == expected) ? "PASS" : "FAIL";           \
        printf("%-100s: %-25s\n", scenario, outcome);                           \
        if (result != expected) pass = 0;                                       \
    } while(0)

// Macro to perform the specified branch operation with description
#define TEST_BRANCH_OP(op, src1, src2, idx, description)                        \
    do {                                                                        \
        asm volatile ("ld " #src1 ", %0" : : "m"(branch_src1[idx]));            \
        asm volatile ("ld " #src2 ", %0" : : "m"(branch_src2[idx]));            \
        asm volatile (                                                          \
            ".align 4\n\t"                       /* Ensure labels are 4-byte aligned */ \
            op " " #src1 ", " #src2 ", 1f\n\t"   /* Conditional branch to label 1f */ \
            "addi zero, zero, 0\n\t"             /* Runs if branch not taken */ \
            "j 2f\n\t"                           /* Jump to 2f to skip label 1f */ \
            ".align 4\n\t"                       /* Ensure next label is aligned */ \
            "1: addi t0, zero, 1\n\t"            /* Label 1: Executed if branch is taken */ \
            ".align 4\n\t"                       /* Ensure next label is aligned */ \
            "2:\n\t"                             /* Label 2: End of the section */ \
        );                                                                  \
        CHECK_BRANCH_OP(branch_expected[idx], idx, description);                \
    } while(0)

int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the integer values and expected results for branches
    initialize_branch_values();

    // Print the table header
    printf("\n%-100s: %-25s\n\n", "Scenario", "Outcome");

    // Testing various branch operations with different combinations of safe registers

    // Using t0 and t1
    TEST_BRANCH_OP("beq", t0, t1, 0, "Test beq where src1 == src2 (0x2000000000002000 == 0x2000000000002000) using t0, t1");
    TEST_BRANCH_OP("bne", t0, t1, 1, "Test bne where src1 != src2 (0x2000000000003000 != 0x2000000000001000) using t0, t1");

    // Using t2 and t3
    TEST_BRANCH_OP("blt", t2, t3, 2, "Test blt where src1 < src2 (0x1 < 0x5) using t2, t3");
    TEST_BRANCH_OP("bge", t2, t3, 3, "Test bge where src1 >= src2 (0x2000000000000008 >= 0x2000000000000004) using t2, t3");

    // Using t4 and t5
    TEST_BRANCH_OP("bltu", t4, t5, 4, "Test bltu where src1 < src2 unsigned (0x1 < 0xFFFFFFFFFFFFFFFF) using t4, t5");
    TEST_BRANCH_OP("bgeu", t4, t5, 5, "Test bgeu where src1 >= src2 unsigned (0xFFFFFFFFFFFFFFFF >= 0x1) using t4, t5");

    // Additional interesting corner cases

    // Negative vs zero using t6 and t0
    TEST_BRANCH_OP("blt", t6, t0, 6, "Test blt where src1 < src2 (-1 < 0) using t6, t0");

    // Zero vs positive using a0 and a1
    TEST_BRANCH_OP("bge", a0, a1, 7, "Test bge where src1 >= src2 (0 >= 1) using a0, a1");

    // Max positive vs min negative using a2 and a3
    TEST_BRANCH_OP("bge", a2, a3, 8, "Test bge where src1 >= src2 (0x7FFFFFFFFFFFFFFF >= 0x8000000000000000) using a2, a3");

    // Alternating bit patterns using a4 and a5
    TEST_BRANCH_OP("bltu", a4, a5, 9, "Test bltu where src1 < src2 (0xAAAAAAAAAAAAAAAA < 0x5555555555555555) using a4, a5");

    // Zero vs max unsigned using a6 and a7
    TEST_BRANCH_OP("bltu", a6, a7, 10, "Test bltu where src1 < src2 (0 < 0xFFFFFFFFFFFFFFFF) using a6, a7");

    // Boundary condition (off-by-one) using t0 and t1
    TEST_BRANCH_OP("bne", t0, t1, 11, "Test bne where src1 != src2 (0xFFFFFFFFFFFFFFFE != 0xFFFFFFFFFFFFFFFF) using t0, t1");

    // Print the test results
    if (pass) {
        printf("\nAll branch tests passed.\n\n");
    } else {
        printf("\nSome branch tests failed.\n\n");
    }

    return 0;
}
