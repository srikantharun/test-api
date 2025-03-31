// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, integer ALU operations are explicitly tested.

#include "common.h"

// Define arrays to store the test values and expected results
uint64_t src1_values[10];
uint64_t src2_values[10];
uint64_t expected_results[10];

// Function to initialize values for testing
void initialize_values() {
    // Initialize source values and expected results for various operations
    src1_values[0] = 0x2000; // Example value 1
    src2_values[0] = 0x2000; // Example value 2
    expected_results[0] = 0x4000; // Expected result for `add`

    src1_values[1] = 0x3000;
    src2_values[1] = 0x1000;
    expected_results[1] = 0x2000; // Expected result for `sub`

    src1_values[2] = 0x4;
    src2_values[2] = 0x5;
    expected_results[2] = 0x14; // Expected result for `mul`

    src1_values[3] = 0x10;
    src2_values[3] = 0x2;
    expected_results[3] = 0x8; // Expected result for `div`

    src1_values[4] = 0x10;
    src2_values[4] = 0x3;
    expected_results[4] = 0x1; // Expected result for `rem`

    src1_values[5] = 0x2000;
    src2_values[5] = 0x2000;
    expected_results[5] = 0x4000; // Expected result for `addw`

    src1_values[6] = 0x3000;
    src2_values[6] = 0x1000;
    expected_results[6] = 0x2000; // Expected result for `subw`

    src1_values[7] = 0x1000;
    src2_values[7] = 0x2;
    expected_results[7] = 0x2000; // Expected result for `mulw`

    src1_values[8] = 0x9;
    src2_values[8] = 0x2;
    expected_results[8] = 0x4; // Expected result for `divw`

    src1_values[9] = 0x9;
    src2_values[9] = 0x2;
    expected_results[9] = 0x1; // Expected result for `remw`
}

// Macro to perform ALU operation and check the result
#define CHECK_OP(dest, expected, idx, scenario)                                \
    do {                                                                       \
        uint64_t dest_val;                                                     \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("mv %0, " #dest : "=r"(dest_val));                       \
        uint64_to_str(dest_val, dest_str);                                     \
        uint64_to_str(expected_results[idx], expected_str);                    \
        const char* result = (dest_val != expected_results[idx]) ? "FAIL" : "PASS"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        if (strcmp(result, "FAIL") == 0) pass = 0;                             \
    } while(0)

// Macro to perform the specified operation with description
#define TEST_OP(op, dest, src1, src2, idx, description)                        \
    do {                                                                       \
        /* Load src1 and src2 values with proper alignment */                  \
        asm volatile ("ld " #src1 ", %0" : : "m"(src1_values[idx]));           \
        asm volatile ("ld " #src2 ", %0" : : "m"(src2_values[idx]));           \
        asm volatile (                                                         \
            ".align 4\n\t"                      /* Align the operation */      \
            op " " #dest ", " #src1 ", " #src2 "\n\t"  /* Execute operation */ \
            ".align 4\n\t"                      /* Align subsequent labels */  \
        );                                                                  \
        CHECK_OP(dest, expected_results[idx], idx, description);               \
    } while(0)


int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the integer values and expected results
    initialize_values();

    // Print the table header
    PRINT_HEADER();

    // Testing various integer ALU operations with different combinations of registers

    // Test all registers except pointer registers (sp, gp, tp)
    TEST_OP("add", t0, t1, t2, 0, "Test addition of 0x2000 and 0x2000 using t0, t1, t2");
    TEST_OP("sub", t3, t4, t5, 1, "Test subtraction of 0x3000 and 0x1000 using t3, t4, t5");
    TEST_OP("mul", t6, s0, s1, 2, "Test multiplication of 0x4 and 0x5 using t6, s0, s1");
    TEST_OP("div", s2, s3, s4, 3, "Test division of 0x10 by 0x2 using s2, s3, s4");
    TEST_OP("rem", s5, s6, s7, 4, "Test remainder of 0x10 by 0x3 using s5, s6, s7");
    TEST_OP("addw", s8, s9, s10, 5, "Test word addition of 0x2000 and 0x2000 using s8, s9, s10");
    TEST_OP("subw", s11, a0, a1, 6, "Test word subtraction of 0x3000 and 0x1000 using s11, a0, a1");
    TEST_OP("mulw", a2, a3, a4, 7, "Test word multiplication of 0x1000 and 0x2 using a2, a3, a4");
    TEST_OP("divw", a5, a6, a7, 8, "Test word division of 0x9 by 0x2 using a5, a6, a7");
    TEST_OP("remw", t0, t1, t2, 9, "Test word remainder of 0x9 by 0x2 using t0, t1, t2");

    // Repeat with different sets of registers for full coverage
    TEST_OP("add", t3, t4, t5, 0, "Test addition using t3, t4, t5 registers");
    TEST_OP("sub", t6, s0, s1, 1, "Test subtraction using t6, s0, s1 registers");
    TEST_OP("mul", s2, s3, s4, 2, "Test multiplication using s2, s3, s4 registers");
    TEST_OP("div", s5, s6, s7, 3, "Test division using s5, s6, s7 registers");
    TEST_OP("rem", s8, s9, s10, 4, "Test remainder using s8, s9, s10 registers");
    TEST_OP("addw", s11, a0, a1, 5, "Test word addition using s11, a0, a1 registers");
    TEST_OP("subw", a2, a3, a4, 6, "Test word subtraction using a2, a3, a4 registers");
    TEST_OP("mulw", a5, a6, a7, 7, "Test word multiplication using a5, a6, a7 registers");
    TEST_OP("divw", t0, t1, t2, 8, "Test word division using t0, t1, t2 registers");
    TEST_OP("remw", t3, t4, t5, 9, "Test word remainder using t3, t4, t5 registers");

    // Continue with other registers until all combinations are covered
    TEST_OP("add", t6, s0, s1, 0, "Test addition using t6, s0, s1 registers");
    TEST_OP("sub", s2, s3, s4, 1, "Test subtraction using s2, s3, s4 registers");
    TEST_OP("mul", s5, s6, s7, 2, "Test multiplication using s5, s6, s7 registers");
    TEST_OP("div", s8, s9, s10, 3, "Test division using s8, s9, s10 registers");
    TEST_OP("rem", s11, a0, a1, 4, "Test remainder using s11, a0, a1 registers");
    TEST_OP("addw", a2, a3, a4, 5, "Test word addition using a2, a3, a4 registers");
    TEST_OP("subw", a5, a6, a7, 6, "Test word subtraction using a5, a6, a7 registers");
    TEST_OP("mulw", t0, t1, t2, 7, "Test word multiplication using t0, t1, t2 registers");
    TEST_OP("divw", t3, t4, t5, 8, "Test word division using t3, t4, t5 registers");
    TEST_OP("remw", t6, s0, s1, 9, "Test word remainder using t6, s0, s1 registers");

    // Adding more combinations with distinct registers and matching indices 0 to 9
    TEST_OP("add", a0, a1, a2, 0, "Test addition using a0, a1, a2 registers");
    TEST_OP("sub", a3, a4, a5, 1, "Test subtraction using a3, a4, a5 registers");
    TEST_OP("mul", a6, a7, s0, 2, "Test multiplication using a6, a7, s0 registers");
    TEST_OP("div", s1, s2, s3, 3, "Test division using s1, s2, s3 registers");
    TEST_OP("rem", s4, s5, s6, 4, "Test remainder using s4, s5, s6 registers");
    TEST_OP("addw", s7, s8, s9, 5, "Test word addition using s7, s8, s9 registers");
    TEST_OP("subw", s10, s11, t0, 6, "Test word subtraction using s10, s11, t0 registers");
    TEST_OP("mulw", t1, t2, t3, 7, "Test word multiplication using t1, t2, t3 registers");
    TEST_OP("divw", t4, t5, t6, 8, "Test word division using t4, t5, t6 registers");
    TEST_OP("remw", a0, a1, a2, 9, "Test word remainder using a0, a1, a2 registers");

    // Print the test results
    if (pass) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }

    return 0;
}
