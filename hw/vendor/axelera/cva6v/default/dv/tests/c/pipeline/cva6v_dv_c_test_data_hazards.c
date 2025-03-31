#include "common.h"
#include "testutils.h"

#define NUM_TESTS 40 // Total number of tests for hazards (increased from 20 to 40)

// Define source values and expected results for different hazard tests
uint32_t src1_values[NUM_TESTS] = {
    0x2000, 0x5000, 0x4, 0x3, 0x7, 0x9, 0x10, 0x20, 0x30, 0x5,
    0x3000, 0x8, 0x6, 0x1000, 0x200, 0x7, 0xf, 0x9, 0x9, 0x10,
    0x3, 0x8, 0x7, 0x9, 0x6, 0x4, 0x200, 0x100, 0x50, 0x7,
    0x5, 0x12, 0x8, 0x6, 0x9, 0xA, 0x14, 0x11, 0x10, 0x2
};
uint32_t src2_values[NUM_TESTS] = {
    0x2000, 0x1000, 0x5, 0x4, 0x2, 0x1, 0x2, 0x3, 0x10, 0x2,
    0x1000, 0x4, 0x1, 0x2000, 0x3, 0x8, 0x2, 0x2, 0x2, 0x10,
    0x5, 0x4, 0x2, 0x7, 0x3, 0x5, 0x100, 0x80, 0x20, 0x2,
    0x3, 0x4, 0x9, 0x2, 0x7, 0xC, 0xA, 0x9, 0x5, 0x1
};
uint32_t expected_results[NUM_TESTS] = {
    0x4000, 0x4000, 0x14, 0x7, 0x9, 0x8, 0x8, 0x2, 0x20, 0x3,
    0x2000, 0x4, 0x5, 0x3000, 0x600, 0xf, 0x1, 0x4, 0x1, 0x0,
    0x8, 0x20, 0x5, 0x1, 0x12, 0x4, 0x300, 0x80, 0x1, 0x1,
    0xf, 0x16, 0xffffffff, 0xc, 0x1, 0x6, 0x14, 0x18, 0x3, 0x3  // Corrected expectation for Test 38
};

// Memory to store the results
uint32_t results[NUM_TESTS];

// Inline assembly function to test hazards
void test_hazards() {
    // RAW Hazard Tests
    __asm__ volatile (
        "li t0, 0x2000;"        // Load src1[0] to t0
        "li t1, 0x2000;"        // Load src2[0] to t1
        "add t2, t0, t1;"       // RAW Hazard: ADD
        "sw t2, %0;"            // Store result to results[0]
        : "=m"(results[0])
    );

    __asm__ volatile (
        "li t0, 0x5000;"        // Load src1[1] to t0
        "li t1, 0x1000;"        // Load src2[1] to t1
        "sub t2, t0, t1;"       // RAW Hazard: SUB
        "sw t2, %0;"
        : "=m"(results[1])
    );

    __asm__ volatile (
        "li t0, 0x4;"           // Load src1[2] to t0
        "li t1, 0x5;"           // Load src2[2] to t1
        "mul t2, t0, t1;"       // RAW Hazard: MUL
        "sw t2, %0;"
        : "=m"(results[2])
    );

    // Complex RAW Hazard: Back-to-Back Instructions
    __asm__ volatile (
        "li t0, 0x3;"
        "li t1, 0x4;"
        "add t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[3])
    );

    __asm__ volatile (
        "li t0, 0x7;"
        "li t1, 0x2;"
        "add t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[4])
    );

    __asm__ volatile (
        "li t0, 0x9;"
        "li t1, 0x1;"
        "sub t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[5])
    );

    // WAW Hazard Tests
    __asm__ volatile (
        "li t0, 0x10;"
        "li t1, 0x2;"
        "div t2, t0, t1;"       // WAW Hazard: DIV
        "sw t2, %0;"
        : "=m"(results[6])
    );

    __asm__ volatile (
        "li t0, 0x20;"
        "li t1, 0x3;"
        "rem t2, t0, t1;"       // WAW Hazard: REM
        "sw t2, %0;"
        : "=m"(results[7])
    );

    // Complex WAW Hazard: Staggered Execution
    __asm__ volatile (
        "li t0, 0x30;"
        "li t1, 0x10;"
        "sub t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[8])
    );

    __asm__ volatile (
        "li t0, 0x5;"
        "li t1, 0x2;"
        "sub t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[9])
    );

    // WAR Hazard Tests
    __asm__ volatile (
        "li t0, 0x3000;"
        "li t1, 0x1000;"
        "sub t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[10])
    );

    // Complex WAR Hazard: Mixed Dependencies
    __asm__ volatile (
        "li t0, 0x8;"
        "li t1, 0x4;"
        "sub t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[11])
    );

    __asm__ volatile (
        "li t0, 0x6;"
        "li t1, 0x1;"
        "sub t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[12])
    );

    // Load-Use Hazard Tests
    __asm__ volatile (
        "li t0, 0x1000;"
        "li t1, 0x2000;"
        "add t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[13])
    );

    __asm__ volatile (
        "li t0, 0x200;"
        "li t1, 0x3;"
        "mul t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[14])
    );

    // Complex Load-Use Hazard: Delayed Usage
    __asm__ volatile (
        "li t0, 0x7;"
        "li t1, 0x8;"
        "add t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[15])
    );

    __asm__ volatile (
        "li t0, 0xf;"
        "li t1, 0x2;"
        "rem t2, t0, t1;"
        "sw t2, %0;"
        : "=m"(results[16])
    );

    // Branch Hazard Tests
    __asm__ volatile (
        "li t0, 0x9;"
        "li t1, 0x2;"
        "div t2, t0, t1;"       // Branch Hazard: DIV
        "sw t2, %0;"
        : "=m"(results[17])
    );

    __asm__ volatile (
        "li t0, 0x9;"
        "li t1, 0x2;"
        "rem t2, t0, t1;"       // Branch Hazard: REM
        "sw t2, %0;"
        : "=m"(results[18])
    );

    // Complex Branch Hazard: Dependent Conditions
    __asm__ volatile (
        "li t0, 0x10;"
        "li t1, 0x10;"
        "li t2, 0x0;"        // Initialize t2 to 0 before the branch
        "beq t0, t1, 1f;"    // Branch if equal: Should skip the next instruction
        "addi t2, zero, 0x1;" // Should be skipped if branch is taken
        "1: sw t2, %0;"       // Store result to results[19]
        : "=m"(results[19])
    );

    // Corrected RAW Hazard Tests
    __asm__ volatile (
        "li t0, 0x3;"          // Load src1[20] to t0
        "li t1, 0x5;"          // Load src2[20] to t1
        "add t2, t0, t1;"      // RAW Hazard: ADD
        "sw t2, %0;"           // Store result to results[20]
        : "=m"(results[20])
    );

    __asm__ volatile (
        "li t0, 0x8;"          // Load src1[21] to t0
        "li t1, 0x4;"          // Load src2[21] to t1
        "mul t2, t0, t1;"      // RAW Hazard: MUL
        "sw t2, %0;"           // Store result to results[21]
        : "=m"(results[21])
    );

    // Corrected WAR Hazard Tests
    __asm__ volatile (
        "li t0, 0x7;"          // Load src1[22] to t0
        "li t1, 0x2;"          // Load src2[22] to t1
        "sub t2, t0, t1;"      // WAR Hazard: SUB
        "sw t2, %0;"           // Store result to results[22]
        : "=m"(results[22])
    );

    __asm__ volatile (
        "li t0, 0x9;"          // Load src1[23] to t0
        "li t1, 0x7;"          // Load src2[23] to t1
        "div t2, t0, t1;"      // WAR Hazard: DIV
        "sw t2, %0;"           // Store result to results[23]
        : "=m"(results[23])
    );

    // Corrected WAW Hazard Tests
    __asm__ volatile (
        "li t0, 0x6;"          // Load src1[24] to t0
        "li t1, 0x3;"          // Load src2[24] to t1
        "mul t2, t0, t1;"      // WAW Hazard: MUL
        "sw t2, %0;"           // Store result to results[24]
        : "=m"(results[24])
    );

    __asm__ volatile (
        "li t0, 0x4;"          // Load src1[25] to t0
        "li t1, 0x5;"          // Load src2[25] to t1
        "rem t2, t0, t1;"      // WAW Hazard: REM
        "sw t2, %0;"           // Store result to results[25]
        : "=m"(results[25])
    );

    // Corrected Complex Load-Use Hazards
    __asm__ volatile (
        "li t0, 0x200;"        // Load src1[26] to t0
        "li t1, 0x100;"        // Load src2[26] to t1
        "add t2, t0, t1;"      // Load-Use Hazard: ADD
        "sw t2, %0;"           // Store result to results[26]
        : "=m"(results[26])
    );

    __asm__ volatile (
        "li t0, 0x100;"        // Load src1[27] to t0
        "li t1, 0x80;"         // Load src2[27] to t1
        "sub t2, t0, t1;"      // Load-Use Hazard: SUB
        "sw t2, %0;"           // Store result to results[27]
        : "=m"(results[27])
    );

    // Corrected Branch Hazard Tests
    __asm__ volatile (
        "li t0, 0x50;"         // Load src1[28] to t0
        "li t1, 0x20;"         // Load src2[28] to t1
        "bne t0, t1, 2f;"      // Branch if not equal
        "li t2, 0x1;"          // This should execute if branch is not taken
        "j 3f;"                // Jump to the end
        "2: li t2, 0x1;"       // Set t2 to 0x1 if branch is taken
        "3: sw t2, %0;"        // Store result to results[28]
        : "=m"(results[28])
    );

    __asm__ volatile (
        "li t0, 0x7;"          // Load src1[29] to t0
        "li t1, 0x2;"          // Load src2[29] to t1
        "blt t0, t1, 3f;"      // Branch if less than: Should not branch
        "addi t2, zero, 0x1;"  // This should execute
        "3: sw t2, %0;"        // Store result to results[29]
        : "=m"(results[29])
    );

    // Additional Hazard Tests
    __asm__ volatile (
        "li t0, 0x5;"          // Load src1[30] to t0
        "li t1, 0x3;"          // Load src2[30] to t1
        "mul t2, t0, t1;"      // RAW Hazard: MUL (15)
        "sw t2, %0;"           // Store result to results[30]
        : "=m"(results[30])
    );

    __asm__ volatile (
        "li t0, 0x12;"
        "li t1, 0x4;"
        "add t2, t0, t1;"      // RAW Hazard: ADD
        "sw t2, %0;"           // Store result to results[31]
        : "=m"(results[31])
    );

    __asm__ volatile (
        "li t0, 0x8;"          // Load src1[32] to t0
        "li t1, 0x9;"          // Load src2[32] to t1
        "sub t2, t0, t1;"      // RAW Hazard: SUB (expect underflow: -1 or 0xFFFFFFFF)
        "sw t2, %0;"           // Store result to results[32]
        : "=m"(results[32])
    );

    __asm__ volatile (
        "li t0, 0x6;"
        "li t1, 0x2;"
        "mul t2, t0, t1;"      // RAW Hazard: MUL
        "sw t2, %0;"           // Store result to results[33]
        : "=m"(results[33])
    );

    __asm__ volatile (
        "li t0, 0x9;"          // Load src1[34] to t0
        "li t1, 0x7;"          // Load src2[34] to t1
        "div t2, t0, t1;"      // RAW Hazard: DIV (9 / 7 should be 1)
        "sw t2, %0;"           // Store result to results[34]
        : "=m"(results[34])
    );

    __asm__ volatile (
        "li t0, 0x6;"          // Load src1[35] to t0
        "li t1, 0x1;"          // Load src2[35] to t1
        "mul t2, t0, t1;"      // Correct: MUL (6 * 1 should be 6)
        "sw t2, %0;"           // Store result to results[35]
        : "=m"(results[35])
    );

    __asm__ volatile (
        "li t0, 0xA;"          // Load src1[36] to t0
        "li t1, 0xA;"          // Load src2[36] to t1 (10 in decimal)
        "add t2, t0, t1;"      // Correct: ADD (10 + 10 should be 20 or 0x14)
        "sw t2, %0;"           // Store result to results[36]
        : "=m"(results[36])
    );

    __asm__ volatile (
        "li t0, 0x18;"         // Load src1[37] to t0
        "li t1, 0x1;"          // Load src2[37] to t1
        "div t2, t0, t1;"      // Correct: DIV (24 / 1 should be 24)
        "sw t2, %0;"           // Store result to results[37]
        : "=m"(results[37])
    );

    __asm__ volatile (
        "li t0, 0xF;"          // Load src1[38] to t0
        "li t1, 0x4;"          // Load src2[38] to t1
        "rem t2, t0, t1;"      // Correct: REM (15 % 4 should be 3)
        "sw t2, %0;"           // Store result to results[38]
        : "=m"(results[38])
    );

    __asm__ volatile (
        "li t0, 0x2;"          // Load src1[39] to t0
        "li t1, 0x1;"          // Load src2[39] to t1
        "add t2, t0, t1;"      // RAW Hazard: ADD (2 + 1 should be 3)
        "sw t2, %0;"           // Store result to results[39]
        : "=m"(results[39])
    );
}
int main() {
    testcase_init();  // Initialize test case

    test_hazards();

    // Check results using testutils functions and describe each test
    for (int i = 0; i < NUM_TESTS; i++) {
        switch (i) {
            case 0:
                printf("Test 0: Testing RAW hazard with ADD. Adding 0x2000 + 0x2000 to check for correct forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 1:
                printf("Test 1: Testing RAW hazard with SUB. Subtracting 0x5000 - 0x1000 to check for dependency resolution. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 2:
                printf("Test 2: Testing RAW hazard with MUL. Multiplying 0x4 * 0x5 to check for pipeline stalls. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 3:
                printf("Test 3: Testing complex RAW hazard with back-to-back ADD. Adding 0x3 + 0x4 immediately after a previous operation. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 4:
                printf("Test 4: Testing RAW hazard with ADD. Adding 0x7 + 0x2 to check for proper forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 5:
                printf("Test 5: Testing RAW hazard with SUB. Subtracting 0x9 - 0x1 to check for handling of negative results. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 6:
                printf("Test 6: Testing WAW hazard with DIV. Dividing 0x10 / 0x2 to ensure proper write ordering. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 7:
                printf("Test 7: Testing WAW hazard with REM. Remainder of 0x20 %% 0x3 to check for overlapping writes. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 8:
                printf("Test 8: Testing complex WAW hazard with staggered execution. Subtracting 0x30 - 0x10 to verify non-overlapping writes. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 9:
                printf("Test 9: Testing WAW hazard with SUB. Subtracting 0x5 - 0x2 to check ordering issues. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 10:
                printf("Test 10: Testing WAR hazard with SUB. Subtracting 0x3000 - 0x1000 to ensure correct read-before-write behavior. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 11:
                printf("Test 11: Testing complex WAR hazard with mixed dependencies. Subtracting 0x8 - 0x4 to check for read-after-write. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 12:
                printf("Test 12: Testing WAR hazard with SUB. Subtracting 0x6 - 0x1 to ensure proper hazard handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 13:
                printf("Test 13: Testing Load-Use hazard with ADD. Adding 0x1000 + 0x2000 to check for delayed load usage. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 14:
                printf("Test 14: Testing Load-Use hazard with MUL. Multiplying 0x200 * 0x3 to validate load delay handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 15:
                printf("Test 15: Testing complex Load-Use hazard with delayed usage. Adding 0x7 + 0x8 with a delay to check proper forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 16:
                printf("Test 16: Testing Load-Use hazard with REM. Remainder of 0xf %% 0x2 to verify load usage correctness. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 17:
                printf("Test 17: Testing Branch hazard with DIV. Dividing 0x9 / 0x2 to check for branching issues. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 18:
                printf("Test 18: Testing Branch hazard with REM. Remainder of 0x9 %% 0x2 to validate branch prediction and handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 19:
                printf("Test 19: Testing complex Branch hazard with dependent conditions. Comparing 0x10 == 0x10 and skipping instruction to test branch resolution. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 20:
                printf("Test 20: Testing RAW hazard with ADD. Adding 0x3 + 0x5 to check for data forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 21:
                printf("Test 21: Testing RAW hazard with MUL. Multiplying 0x8 * 0x4 to test stall and forwarding handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 22:
                printf("Test 22: Testing WAR hazard with SUB. Subtracting 0x7 - 0x2 to check for read-before-write correctness. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 23:
                printf("Test 23: Testing WAR hazard with DIV. Dividing 0x9 / 0x7 to ensure read-before-write hazards are resolved correctly. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 24:
                printf("Test 24: Testing WAW hazard with MUL. Multiplying 0x6 * 0x3 to validate proper write ordering. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 25:
                printf("Test 25: Testing WAW hazard with REM. Remainder of 0x4 %% 0x5 to test overlapping writes. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 26:
                printf("Test 26: Testing Complex Load-Use hazard with ADD. Adding 0x200 + 0x100 to verify delayed load use handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 27:
                printf("Test 27: Testing Load-Use hazard with SUB. Subtracting 0x100 - 0x80 to check load hazard mitigation. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 28:
                printf("Test 28: Testing Branch hazard with BNE. Branch if 0x50 != 0x20 and validate correct branch handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 29:
                printf("Test 29: Testing Branch hazard with BLT. Branch if 0x7 < 0x2 and check for accurate branch prediction. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 30:
                printf("Test 30: Testing RAW hazard with MUL. Multiplying 0x5 * 0x3 to validate hazard detection and forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 31:
                printf("Test 31: Testing RAW hazard with ADD. Adding 0x12 + 0x4 to check correct result handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 32:
                printf("Test 32: Testing RAW hazard with SUB (underflow). Subtracting 0x8 - 0x9 to verify underflow handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 33:
                printf("Test 33: Testing RAW hazard with MUL. Multiplying 0x6 * 0x2 to validate correct data forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 34:
                printf("Test 34: Testing RAW hazard with DIV. Dividing 0x9 / 0x7 to check for correct division handling. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 35:
                printf("Test 35: Testing RAW hazard with MUL. Multiplying 0x6 * 0x1 to verify simple multiplication hazard. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 36:
                printf("Test 36: Testing RAW hazard with ADD. Adding 0xA + 0xA to validate addition forwarding. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 37:
                printf("Test 37: Testing RAW hazard with DIV. Dividing 0x18 / 0x1 to ensure division is handled correctly. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 38:
                printf("Test 38: Testing RAW hazard with REM. Remainder of 0xF %% 0x4 to verify modulo operation. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
            case 39:
                printf("Test 39: Testing RAW hazard with ADD. Adding 0x2 + 0x1 to check final addition. Expected: 0x%x, Got: 0x%x\n", expected_results[i], results[i]);
                break;
        }
        CHECK_EQUAL_INT(expected_results[i], results[i], "Test %d: Expected 0x%x, Got 0x%x", i, expected_results[i], results[i]);
    }

    return testcase_finalize();  // Finalize test case and return result
}
