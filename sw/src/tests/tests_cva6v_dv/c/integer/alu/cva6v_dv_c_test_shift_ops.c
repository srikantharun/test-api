// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, shift instructions are explicitly tested.

#include "common.h"

// Define arrays to store the test values for shift instructions
__attribute__((aligned(8))) uint64_t shift_src1[16];
__attribute__((aligned(8))) uint64_t shift_src2[16];
uint64_t expected_shift_results[16];

// Function to initialize values for testing shift instructions
void initialize_shift_values() {
    // Basic shift tests
    shift_src1[0] = 0x1; // Shift left test for `sll`
    shift_src2[0] = 3;
    expected_shift_results[0] = 0x8; // Expected result 1 << 3 = 8

    shift_src1[1] = 0x8; // Shift right logical test for `srl`
    shift_src2[1] = 3;
    expected_shift_results[1] = 0x1; // Expected result 8 >> 3 = 1

    shift_src1[2] = 0xFFFFFFFFFFFFFFFF; // Shift right arithmetic test for `sra`
    shift_src2[2] = 1;
    expected_shift_results[2] = 0xFFFFFFFFFFFFFFFF; // Expected result -1 >> 1 = -1

    shift_src1[3] = 0x7FFFFFFF; // Shift left word test for `sllw`
    shift_src2[3] = 1;
    expected_shift_results[3] = 0xFFFFFFFE; // Expected 32-bit result 0x7FFFFFFF << 1

    shift_src1[4] = 0xFFFFFFFE; // Shift right logical word test for `srlw`
    shift_src2[4] = 1;
    expected_shift_results[4] = 0x7FFFFFFF; // Expected 32-bit result 0xFFFFFFFE >> 1

    shift_src1[5] = 0xFFFFFFFF80000000; // Shift right arithmetic word test for `sraw`
    shift_src2[5] = 4;
    expected_shift_results[5] = 0xFFFFFFFFF8000000; // Expected 32-bit signed right shift

    // Additional corner cases
    shift_src1[6] = 0xAAAAAAAAAAAAAAAA; // Alternating bit pattern for `sll`
    shift_src2[6] = 4;
    expected_shift_results[6] = 0xAAAAAAAAAAAAAAAA << 4; // Expected shift left result

    shift_src1[7] = 0x0000000F00000000; // High byte set for `srl`
    shift_src2[7] = 8;
    expected_shift_results[7] = 0x000000000F000000; // Expected shift right logical

    shift_src1[8] = 0x8000000000000000; // Highest bit set for `sra`
    shift_src2[8] = 63;
    expected_shift_results[8] = 0xFFFFFFFFFFFFFFFF; // Expected right shift arithmetic

    shift_src1[9] = 0xFFFFFFFF; // 32-bit shift arithmetic left using `sllw`
    shift_src2[9] = 2;
    expected_shift_results[9] = 0xFFFFFFFC; // Expected 32-bit result

    shift_src1[10] = 0xFFFFFFFF; // 32-bit shift logical right using `srlw`
    shift_src2[10] = 2;
    expected_shift_results[10] = 0x3FFFFFFF; // Expected 32-bit result

    shift_src1[11] = 0x80000000; // 32-bit shift arithmetic right using `sraw`
    shift_src2[11] = 1;
    expected_shift_results[11] = 0xC0000000; // Expected 32-bit result signed shift

    // Famous shift operation bugs and additional edge cases
    shift_src1[12] = 0x0000000100000000; // Large shift counts for `srl`
    shift_src2[12] = 33;                 // Shifting more than 32 bits can cause errors
    expected_shift_results[12] = 0x0000000008000000; // Expected shift right

    shift_src1[13] = 0xFFFFFFFFFFFFFFFF; // Max negative with `sraw`
    shift_src2[13] = 63;                 // Test maximum shift amount
    expected_shift_results[13] = 0xFFFFFFFFFFFFFFFF; // Expected arithmetic right shift of -1

    shift_src1[14] = 0x7FFFFFFFFFFFFFFF; // Maximum positive 64-bit for `sra`
    shift_src2[14] = 1;
    expected_shift_results[14] = 0x3FFFFFFFFFFFFFFF; // Expected result of right shift

    shift_src1[15] = 0x1; // Shifting by zero `sllw`, should be no-op
    shift_src2[15] = 0;
    expected_shift_results[15] = 0x1; // Expected result no change
}

// Macro to perform shift test and check the result
#define CHECK_SHIFT_OP(dest, expected, idx, scenario)                           \
    do {                                                                        \
        uint64_t dest_val;                                                      \
        asm volatile ("mv %0, " #dest : "=r"(dest_val));                        \
        const char *outcome = (dest_val != expected_shift_results[idx]) ? "FAIL" : "PASS"; \
        printf("dest: 0x%016llx expectation: 0x%016llx %-80s\n\n", dest_val, expected_shift_results[idx], outcome); \
        if (dest_val != expected_shift_results[idx]) pass = 0;                  \
    } while (0)

// Macro to perform the specified shift operation with description
#define TEST_SHIFT_OP(op, dest, src1, src2, idx, description)                   \
    do {                                                                        \
        asm volatile ("ld " #src1 ", %0" : : "m"(shift_src1[idx]));             \
        asm volatile ("ld " #src2 ", %0" : : "m"(shift_src2[idx]));             \
        printf("%-60s with src1=0x%llx, src2=0x%llx using %s, %s, %s: ",        \
               description, shift_src1[idx], shift_src2[idx], #dest, #src1, #src2); \
        asm volatile (op " " #dest ", " #src1 ", " #src2);                      \
        CHECK_SHIFT_OP(dest, expected_shift_results[idx], idx, description);    \
    } while (0)

int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize the shift values and expected results
    initialize_shift_values();

    // Print the table header
    printf("\n%-100s  %-80s\n", "Scenario :",  "Result");

    // Testing various shift operations with different combinations of `t` and `a` registers

    // Using t0, t1, t2
    TEST_SHIFT_OP("sll", t0, t1, t2, 0, "Test shift left logical (sll). Expected result: 1 << 3 = 8, shifting 0x1 left by 3 bits.");

    // Using t3, t4, t5
    TEST_SHIFT_OP("srl", t3, t4, t5, 1, "Test shift right logical (srl). Expected result: 8 >> 3 = 1, shifting 0x8 right by 3 bits.");

    // Using t6, t0, t1
    TEST_SHIFT_OP("sra" , t6, t0, t1, 2, "Test shift right arithmetic (sra). Expected result: -1 >> 1 = -1, shifting 0xFFFFFFFFFFFFFFFF right by 1 bit keeping the sign.");

    // Using t2, t3, t4
    TEST_SHIFT_OP("sllw", t2, t3, t4, 3, "Test shift left logical word (sllw). Expected result: 0x7FFFFFFF << 1 = 0xFFFFFFFE, 32-bit shift left with sign extension.");

    // Using t5, t6, t0
    TEST_SHIFT_OP("srlw", t5, t6, t0, 4, "Test shift right logical word (srlw). Expected result: 0xFFFFFFFE >> 1 = 0x7FFFFFFF, 32-bit logical shift right.");

    // Using t1, t2, t3
    TEST_SHIFT_OP("sraw", t1, t2, t3, 5, "Test shift right arithmetic word (sraw). Expected result: 0xFFFFFFFF80000000 >> 4 = 0xFFFFFFFFF8000000, signed right shift.");

    // Additional corner cases using only `t` and `a` registers

    // Using t4, t5, t6
    TEST_SHIFT_OP("sll" , t4, t5, t6, 6, "Test sll with alternating bit pattern. Expected result: 0xAAAAAAAAAAAAAAAA << 4, shift left of alternating bits.");

    // Using a0, a1, a2
    TEST_SHIFT_OP("srl" , a0, a1, a2, 7, "Test srl with high byte set. Expected result: 0x0000000F00000000 >> 8 = 0x000000000F000000, logical shift right.");

    // Using a3, a4, a5
    TEST_SHIFT_OP("sra" , a3, a4, a5, 8, "Test sra with highest bit set. Expected result: 0x8000000000000000 >> 63 = 0xFFFFFFFFFFFFFFFF, shifting the highest bit keeping sign.");

    // Using a6, a7, t0
    TEST_SHIFT_OP("sllw", a6, a7, t0, 9, "Test sllw 32-bit with full 32-bits. Expected result: 0xFFFFFFFF << 2 = 0xFFFFFFFC, 32-bit shift left.");

    // Using t0, t1, t2
    TEST_SHIFT_OP("srlw", t0, t1, t2, 10, "Test srlw 32-bit with full 32-bits. Expected result: 0xFFFFFFFF >> 2 = 0x3FFFFFFF, 32-bit logical right shift.");

    // Using t3, t4, t5
    TEST_SHIFT_OP("sraw", t3, t4, t5, 11, "Test sraw 32-bit arithmetic right shift. Expected result: 0x80000000 >> 1 = 0xC0000000, signed arithmetic right shift.");

    // Using a0, a1, a2
    TEST_SHIFT_OP("srl" , a0, a1, a2, 12, "Test srl with large shift count. Expected result: 0x100000000 >> 33, checking large shift counts beyond word size.");

    // Using a3, a4, a5
    TEST_SHIFT_OP("sraw", a3, a4, a5, 13, "Test sraw with max negative shift. Expected result: 0xFFFFFFFFFFFFFFFF >> 63 = 0xFFFFFFFFFFFFFFFF, arithmetic shift of max negative.");

    // Using a6, a7, t0
    TEST_SHIFT_OP("sra" , a6, a7, t0, 14, "Test sra with max positive shift. Expected result: 0x7FFFFFFFFFFFFFFF >> 1 = 0x3FFFFFFFFFFFFFFF, right shifting max positive.");

    // Using t1, t2, t3
    TEST_SHIFT_OP("sllw", t1, t2, t3, 15, "Test sllw with zero shift amount. Expected result: 0x1 << 0 = 0x1, ensuring zero shift does not alter value.");

    // Print the test results
    printf("\n");
    if (pass) {
        printf("All shift tests passed.\n\n");
    } else {
        printf("Some shift tests failed.\n\n");
    }

    return 0;
}
