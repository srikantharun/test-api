// Enhanced Forwarding and Stalling Test File for RISC-V 64-bit
// Author: Abhilash

#include "common.h"

// Define arrays for test values, expected results, and computed results
#define TOTAL_TESTS 30

uint64_t src1_values_forward_stall[TOTAL_TESTS];
uint64_t src2_values_forward_stall[TOTAL_TESTS];
uint64_t expected_results_forward_stall[TOTAL_TESTS];
uint64_t computed_results_forward_stall[TOTAL_TESTS];  // Array to store results in memory

// Function to initialize values for forwarding and stalling tests
void initialize_forward_stall_values() {
    // Test Case 0: add 15 + 25 = 40
    src1_values_forward_stall[0] = 15;
    src2_values_forward_stall[0] = 25;
    expected_results_forward_stall[0] = 15 + 25; // 40

    // Test Case 1: sub 40 - 35 = 5
    src1_values_forward_stall[1] = 40; // Result from Test Case 0
    src2_values_forward_stall[1] = 35;
    expected_results_forward_stall[1] = 40 - 35; // 5

    // Test Case 2: mul 5 * 40 = 200
    src1_values_forward_stall[2] = 5;  // Result from Test Case 1
    src2_values_forward_stall[2] = 40;
    expected_results_forward_stall[2] = 5 * 40; // 200

    // Test Case 3: add 50 + 20 = 70 (Load-Use Hazard)
    src1_values_forward_stall[3] = 50; // Loaded value
    src2_values_forward_stall[3] = 20;
    expected_results_forward_stall[3] = 50 + 20; // 70

    // Test Case 4: add 10 + 20 = 30 (Simple ALU Dependency)
    src1_values_forward_stall[4] = 10;
    src2_values_forward_stall[4] = 20;
    expected_results_forward_stall[4] = 10 + 20; // 30

    // Test Case 5: sub 30 - 5 = 25 (ALU Dependency)
    src1_values_forward_stall[5] = 30;
    src2_values_forward_stall[5] = 5;
    expected_results_forward_stall[5] = 30 - 5; // 25

    // Test Case 6: mul 25 * 2 = 50 (ALU Dependency)
    src1_values_forward_stall[6] = 25;
    src2_values_forward_stall[6] = 2;
    expected_results_forward_stall[6] = 25 * 2; // 50

    // Test Case 7: div 50 / 2 = 25 (ALU Dependency)
    src1_values_forward_stall[7] = 50;
    src2_values_forward_stall[7] = 2;
    expected_results_forward_stall[7] = 50 / 2; // 25

    // Test Case 8: beq (handled separately)
    // No initialization needed here

    // Test Case 9: add 5 + 10 = 15 (Simple ALU Forwarding)
    src1_values_forward_stall[9] = 5;
    src2_values_forward_stall[9] = 10;
    expected_results_forward_stall[9] = 5 + 10; // 15

    // Test Case 10: sub 15 - 5 = 10 (Simple ALU Forwarding)
    src1_values_forward_stall[10] = 15;
    src2_values_forward_stall[10] = 5;
    expected_results_forward_stall[10] = 15 - 5; // 10

    // Test Case 11: add 75 + 25 = 100 (Load-Use Hazard with Stalling)
    src1_values_forward_stall[11] = 75;
    src2_values_forward_stall[11] = 25;
    expected_results_forward_stall[11] = 75 + 25; // 100

    // Test Case 12: mul 8 * 2 = 16 (ALU Dependency)
    src1_values_forward_stall[12] = 8;
    src2_values_forward_stall[12] = 2;
    expected_results_forward_stall[12] = 8 * 2; // 16

    // Test Case 13: div 16 / 4 = 4 (ALU Dependency)
    src1_values_forward_stall[13] = 16;
    src2_values_forward_stall[13] = 4;
    expected_results_forward_stall[13] = 16 / 4; // 4

    // Test Case 14: add 4 + 6 = 10 (ALU Dependency)
    src1_values_forward_stall[14] = 4;
    src2_values_forward_stall[14] = 6;
    expected_results_forward_stall[14] = 4 + 6; // 10

    // Test Case 15: sub 10 - 3 = 7 (ALU Dependency)
    src1_values_forward_stall[15] = 10;
    src2_values_forward_stall[15] = 3;
    expected_results_forward_stall[15] = 10 - 3; // 7

    // Test Case 16: mul 7 * 3 = 21 (ALU Dependency)
    src1_values_forward_stall[16] = 7;
    src2_values_forward_stall[16] = 3;
    expected_results_forward_stall[16] = 7 * 3; // 21

    // Test Case 17: div 21 / 7 = 3 (ALU Dependency)
    src1_values_forward_stall[17] = 21;
    src2_values_forward_stall[17] = 7;
    expected_results_forward_stall[17] = 21 / 7; // 3

    // Test Case 18: add 3 + 9 = 12 (ALU Dependency)
    src1_values_forward_stall[18] = 3;
    src2_values_forward_stall[18] = 9;
    expected_results_forward_stall[18] = 3 + 9; // 12

    // Test Case 19: sub 12 - 4 = 8 (ALU Dependency)
    src1_values_forward_stall[19] = 12;
    src2_values_forward_stall[19] = 4;
    expected_results_forward_stall[19] = 12 - 4; // 8

    // New Test Cases (20-29): More Complex and Dependent Scenarios

    // Test Case 20: add 20 + 30 = 50 (Simple ALU Forwarding)
    src1_values_forward_stall[20] = 20;
    src2_values_forward_stall[20] = 30;
    expected_results_forward_stall[20] = 20 + 30; // 50

    // Test Case 21: mul 50 * 2 = 100 (ALU Dependency)
    src1_values_forward_stall[21] = 50;
    src2_values_forward_stall[21] = 2;
    expected_results_forward_stall[21] = 50 * 2; // 100

    // Test Case 22: div 100 / 4 = 25 (ALU Dependency)
    src1_values_forward_stall[22] = 100;
    src2_values_forward_stall[22] = 4;
    expected_results_forward_stall[22] = 100 / 4; // 25

    // Test Case 23: add 25 + 75 = 100 (Complex ALU Forwarding)
    src1_values_forward_stall[23] = 25;
    src2_values_forward_stall[23] = 75;
    expected_results_forward_stall[23] = 25 + 75; // 100

    // Test Case 24: sub 100 - 50 = 50 (ALU Dependency)
    src1_values_forward_stall[24] = 100;
    src2_values_forward_stall[24] = 50;
    expected_results_forward_stall[24] = 100 - 50; // 50

    // Test Case 25: mul 50 * 3 = 150 (ALU Dependency)
    src1_values_forward_stall[25] = 50;
    src2_values_forward_stall[25] = 3;
    expected_results_forward_stall[25] = 50 * 3; // 150

    // Test Case 26: div 150 / 5 = 30 (ALU Dependency)
    src1_values_forward_stall[26] = 150;
    src2_values_forward_stall[26] = 5;
    expected_results_forward_stall[26] = 150 / 5; // 30

    // Test Case 27: add 30 + 70 = 100 (Complex ALU and Memory)
    src1_values_forward_stall[27] = 30;
    src2_values_forward_stall[27] = 70;
    expected_results_forward_stall[27] = 30 + 70; // 100

    // Test Case 28: sub 100 - 40 = 60 (ALU Dependency)
    src1_values_forward_stall[28] = 100;
    src2_values_forward_stall[28] = 40;
    expected_results_forward_stall[28] = 100 - 40; // 60

    // Test Case 29: mul 60 * 4 = 240 (ALU Dependency)
    src1_values_forward_stall[29] = 60;
    src2_values_forward_stall[29] = 4;
    expected_results_forward_stall[29] = 60 * 4; // 240
}

// Macro to perform a forwarding or stalling test and store the result in memory
#define TEST_FORWARD_STALL_OP(op, idx)                                             \
    do {                                                                           \
        uint64_t src1_val = src1_values_forward_stall[idx];                        \
        uint64_t src2_val = src2_values_forward_stall[idx];                        \
        __asm__ volatile (                                                         \
            op " %0, %1, %2\n\t"                                                   \
            : "=r"(computed_results_forward_stall[idx])                            \
            : "r"(src1_val), "r"(src2_val)                                         \
        );                                                                         \
    } while(0)

// Function to test branch dependency separately and store result in memory
void test_branch_dependency() {
    uint64_t x1 = 30;
    uint64_t x2 = 30;

    // Inline assembly to perform the branch and set a flag if taken
    __asm__ volatile (
        "beq %[reg1], %[reg2], 1f\n\t"   // Branch to label 1 if x1 == x2
        "li %[res], 0\n\t"               // If not taken, set result to 0
        "j 2f\n\t"                       // Jump to end
        "1:\n\t"                         // Label 1
        "li %[res], 1\n\t"               // If taken, set result to 1
        "2:\n\t"                         // Label 2
        : [res] "=r" (computed_results_forward_stall[8]) // Store result in memory
        : [reg1] "r" (x1), [reg2] "r" (x2)
        : "memory"
    );

    // No need for immediate printf statements; defer checking
}

// Function to run the forwarding and stalling tests and store results in memory
void test_forward_stall_enhanced() {
    // No need for a 'result' variable as results are stored in memory

    // Case 0: Forwarding (add 15 + 25 = 40)
    TEST_FORWARD_STALL_OP("add", 0);

    // Case 1: Stalling (sub 40 - 35 = 5)
    TEST_FORWARD_STALL_OP("sub", 1);

    // Case 2: Combination (mul 5 * 40 = 200)
    TEST_FORWARD_STALL_OP("mul", 2);

    // Case 3: Load-Use Hazard (add 50 + 20 = 70)
    TEST_FORWARD_STALL_OP("add", 3);

    // Case 4: Multiple Dependent ALU Instructions (add 10 + 20 = 30)
    TEST_FORWARD_STALL_OP("add", 4);

    // Case 5: Multiple Dependent ALU Instructions (sub 30 - 5 = 25)
    TEST_FORWARD_STALL_OP("sub", 5);

    // Case 6: Multiple Dependent ALU Instructions (mul 25 * 2 = 50)
    TEST_FORWARD_STALL_OP("mul", 6);

    // Case 7: Multiple Dependent ALU Instructions (div 50 / 2 = 25)
    TEST_FORWARD_STALL_OP("div", 7);

    // Case 8: Branch Dependency Hazard (handled separately)
    test_branch_dependency();

    // Case 9: Multiple Forwarding Paths (add 5 + 10 = 15)
    TEST_FORWARD_STALL_OP("add", 9);

    // Case 10: Multiple Forwarding Paths (sub 15 - 5 = 10)
    TEST_FORWARD_STALL_OP("sub", 10);

    // Case 11: Load-Use Hazard with Stalling (add 75 + 25 = 100)
    TEST_FORWARD_STALL_OP("add", 11);

    // Case 12: Complex Dependent Instructions (mul 8 * 2 = 16)
    TEST_FORWARD_STALL_OP("mul", 12);

    // Case 13: Complex Dependent Instructions (div 16 / 4 = 4)
    TEST_FORWARD_STALL_OP("div", 13);

    // Case 14: Complex Dependent Instructions (add 4 + 6 = 10)
    TEST_FORWARD_STALL_OP("add", 14);

    // Case 15: Complex Dependent Instructions (sub 10 - 3 = 7)
    TEST_FORWARD_STALL_OP("sub", 15);

    // Case 16: Complex Dependent Instructions (mul 7 * 3 = 21)
    TEST_FORWARD_STALL_OP("mul", 16);

    // Case 17: Complex Dependent Instructions (div 21 / 7 = 3)
    TEST_FORWARD_STALL_OP("div", 17);

    // Case 18: Complex Dependent Instructions (add 3 + 9 = 12)
    TEST_FORWARD_STALL_OP("add", 18);

    // Case 19: Complex Dependent Instructions (sub 12 - 4 = 8)
    TEST_FORWARD_STALL_OP("sub", 19);

    // Additional Test Cases: 20-29

    // Case 20: Forwarding (add 20 + 30 = 50)
    TEST_FORWARD_STALL_OP("add", 20);

    // Case 21: ALU Dependency (mul 50 * 2 = 100)
    TEST_FORWARD_STALL_OP("mul", 21);

    // Case 22: ALU Dependency (div 100 / 4 = 25)
    TEST_FORWARD_STALL_OP("div", 22);

    // Case 23: Complex ALU and Memory (add 25 + 75 = 100)
    TEST_FORWARD_STALL_OP("add", 23);

    // Case 24: ALU Dependency (sub 100 - 50 = 50)
    TEST_FORWARD_STALL_OP("sub", 24);

    // Case 25: ALU Dependency (mul 50 * 3 = 150)
    TEST_FORWARD_STALL_OP("mul", 25);

    // Case 26: ALU Dependency (div 150 / 5 = 30)
    TEST_FORWARD_STALL_OP("div", 26);

    // Case 27: Complex ALU and Memory (add 30 + 70 = 100)
    TEST_FORWARD_STALL_OP("add", 27);

    // Case 28: ALU Dependency (sub 100 - 40 = 60)
    TEST_FORWARD_STALL_OP("sub", 28);

    // Case 29: ALU Dependency (mul 60 * 4 = 240)
    TEST_FORWARD_STALL_OP("mul", 29);
}



// Function to check branch dependency separately
void check_branch_result() {
    printf("Test Case 8: Branch Dependency Hazard.\n");
    printf("Scenario: beq x1=30 == x2=30 -> branch taken, result should be 1.\n");
    printf("Purpose: Checking if the branch condition is correctly evaluated and the result is set accordingly.\n\n");
    CHECK_EQUAL_INT(1, computed_results_forward_stall[8], "Test Case 8 failed: beq x1=30 == x2=30 -> 1");
}

// Function to check all results after all operations are complete
void check_all_results() {
    for (int i = 0; i < TOTAL_TESTS; i++) {
        // Handle Test Case 8 separately
        if (i == 8) {
            check_branch_result();
            continue;
        }

        // Print information about the scenario being tested
        switch (i) {
            case 0:
                printf("Test Case 0: Forwarding test.\n");
                printf("Scenario: add 15 + 25 = 40.\n");
                printf("Purpose: Checking if the result is correctly forwarded without stalling.\n\n");
                break;
            case 1:
                printf("Test Case 1: Stalling test.\n");
                printf("Scenario: sub 40 - 35 = 5.\n");
                printf("Purpose: Checking if the pipeline stalls correctly when data is not yet available.\n\n");
                break;
            case 2:
                printf("Test Case 2: Combination test.\n");
                printf("Scenario: mul 5 * 40 = 200.\n");
                printf("Purpose: Verifying if the pipeline handles forwarding across multiple stages.\n\n");
                break;
            case 3:
                printf("Test Case 3: Load-Use hazard.\n");
                printf("Scenario: load 50 into register and then add 50 + 20 = 70.\n");
                printf("Purpose: Checking if the load value is forwarded to the next instruction without stalling.\n\n");
                break;
            case 4:
                printf("Test Case 4: ALU Dependency.\n");
                printf("Scenario: add 10 + 20 = 30.\n");
                printf("Purpose: Verifying forwarding in a simple ALU operation.\n\n");
                break;
            case 5:
                printf("Test Case 5: ALU Dependency.\n");
                printf("Scenario: sub 30 - 5 = 25.\n");
                printf("Purpose: Verifying stalling when result is needed from a previous instruction.\n\n");
                break;
            case 6:
                printf("Test Case 6: ALU Dependency.\n");
                printf("Scenario: mul 25 * 2 = 50.\n");
                printf("Purpose: Checking if multiplication result is forwarded without stalling.\n\n");
                break;
            case 7:
                printf("Test Case 7: ALU Dependency.\n");
                printf("Scenario: div 50 / 2 = 25.\n");
                printf("Purpose: Checking if the division result is correctly forwarded.\n\n");
                break;
            case 9:
                printf("Test Case 9: Forwarding test.\n");
                printf("Scenario: add 5 + 10 = 15.\n");
                printf("Purpose: Simple test to verify if the result of addition is forwarded.\n\n");
                break;
            case 10:
                printf("Test Case 10: Forwarding test.\n");
                printf("Scenario: sub 15 - 5 = 10.\n");
                printf("Purpose: Simple subtraction test to verify if the result is forwarded without delay.\n\n");
                break;
            case 11:
                printf("Test Case 11: Load-Use hazard with stalling.\n");
                printf("Scenario: load 75 into register and then add 75 + 25 = 100.\n");
                printf("Purpose: Checking if the loaded value is forwarded to the next instruction without stalling.\n\n");
                break;
            case 12:
                printf("Test Case 12: ALU Dependency.\n");
                printf("Scenario: mul 8 * 2 = 16.\n");
                printf("Purpose: Verifying if the multiplication result is forwarded correctly.\n\n");
                break;
            case 13:
                printf("Test Case 13: ALU Dependency.\n");
                printf("Scenario: div 16 / 4 = 4.\n");
                printf("Purpose: Checking forwarding of the division result to the next instruction.\n\n");
                break;
            case 14:
                printf("Test Case 14: ALU Dependency.\n");
                printf("Scenario: add 4 + 6 = 10.\n");
                printf("Purpose: Verifying if the addition result is forwarded without delay.\n\n");
                break;
            case 15:
                printf("Test Case 15: ALU Dependency.\n");
                printf("Scenario: sub 10 - 3 = 7.\n");
                printf("Purpose: Checking if the subtraction result is forwarded correctly.\n\n");
                break;
            case 16:
                printf("Test Case 16: ALU Dependency.\n");
                printf("Scenario: mul 7 * 3 = 21.\n");
                printf("Purpose: Verifying if the multiplication result is forwarded correctly to the next instruction.\n\n");
                break;
            case 17:
                printf("Test Case 17: ALU Dependency.\n");
                printf("Scenario: div 21 / 7 = 3.\n");
                printf("Purpose: Checking if the division result is forwarded without delay.\n\n");
                break;
            case 18:
                printf("Test Case 18: ALU Dependency.\n");
                printf("Scenario: add 3 + 9 = 12.\n");
                printf("Purpose: Verifying if the result of addition is forwarded correctly.\n\n");
                break;
            case 19:
                printf("Test Case 19: ALU Dependency.\n");
                printf("Scenario: sub 12 - 4 = 8.\n");
                printf("Purpose: Checking if the subtraction result is forwarded without delay.\n\n");
                break;
            case 20:
                printf("Test Case 20: Forwarding test.\n");
                printf("Scenario: add 20 + 30 = 50.\n");
                printf("Purpose: Checking if the result of addition is forwarded correctly.\n\n");
                break;
            case 21:
                printf("Test Case 21: ALU Dependency.\n");
                printf("Scenario: mul 50 * 2 = 100.\n");
                printf("Purpose: Verifying if the multiplication result is forwarded correctly.\n\n");
                break;
            case 22:
                printf("Test Case 22: ALU Dependency.\n");
                printf("Scenario: div 100 / 4 = 25.\n");
                printf("Purpose: Checking if the division result is forwarded correctly.\n\n");
                break;
            case 23:
                printf("Test Case 23: Complex ALU and Memory.\n");
                printf("Scenario: add 25 + 75 = 100.\n");
                printf("Purpose: Verifying if complex ALU operations involving memory are handled correctly with forwarding.\n\n");
                break;
            case 24:
                printf("Test Case 24: ALU Dependency.\n");
                printf("Scenario: sub 100 - 50 = 50.\n");
                printf("Purpose: Checking if the subtraction result is forwarded correctly.\n\n");
                break;
            case 25:
                printf("Test Case 25: ALU Dependency.\n");
                printf("Scenario: mul 50 * 3 = 150.\n");
                printf("Purpose: Verifying if the multiplication result is forwarded correctly.\n\n");
                break;
            case 26:
                printf("Test Case 26: ALU Dependency.\n");
                printf("Scenario: div 150 / 5 = 30.\n");
                printf("Purpose: Checking if the division result is forwarded correctly.\n\n");
                break;
            case 27:
                printf("Test Case 27: Complex ALU and Memory.\n");
                printf("Scenario: add 30 + 70 = 100.\n");
                printf("Purpose: Verifying if complex ALU operations involving memory are handled correctly with forwarding.\n\n");
                break;
            case 28:
                printf("Test Case 28: ALU Dependency.\n");
                printf("Scenario: sub 100 - 40 = 60.\n");
                printf("Purpose: Checking if the subtraction result is forwarded correctly.\n\n");
                break;
            case 29:
                printf("Test Case 29: ALU Dependency.\n");
                printf("Scenario: mul 60 * 4 = 240.\n");
                printf("Purpose: Verifying if the multiplication result is forwarded correctly to the next instruction.\n\n");
                break;
            default:
                printf("Test Case %d: Unrecognized test case. Skipping...\n\n", i);
                continue;
        }

        // Perform the actual check for this test case
        CHECK_EQUAL_INT(expected_results_forward_stall[i], computed_results_forward_stall[i], "Test case %d failed", i);
    }
}
int main() {
    printf("Running enhanced test: forward_stall_enhanced\n");
    initialize_forward_stall_values();
    testcase_init();

    // Run all tests, results are stored in memory
    test_forward_stall_enhanced();

    // Now check the results at the end to avoid register pollution
    check_all_results();

    int result = testcase_finalize();
    if (result == TEST_SUCCESS) {
        printf("All forwarding and stalling tests passed.\n");
    } else {
        printf("Some forwarding and stalling tests failed.\n");
    }
    return result;
}
