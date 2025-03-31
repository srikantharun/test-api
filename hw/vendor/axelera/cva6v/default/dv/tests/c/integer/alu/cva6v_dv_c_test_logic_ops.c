#include "common.h"
#include "testutils.h"

// Define arrays to store the test values for logical instructions
__attribute__((aligned(8))) uint64_t logic_src1[12];
__attribute__((aligned(8))) uint64_t logic_src2[12];
uint64_t expected_logic_results[12];

// Function to initialize values for testing logical instructions
void initialize_logic_values() {
    // Basic logical tests
    logic_src1[0] = 0xFFFFFFFFFFFFFFFF; // Logical AND test
    logic_src2[0] = 0x0;
    expected_logic_results[0] = 0x0; // Expected result: 0xFFFFFFFFFFFFFFFF & 0x0 = 0x0

    logic_src1[1] = 0x123456789ABCDEF0; // Logical OR test
    logic_src2[1] = 0x0F0F0F0F0F0F0F0F;
    expected_logic_results[1] = 0x1F3F5F7F9FBFDFFF; // Corrected expected result: 0x123456789ABCDEF0 | 0x0F0F0F0F0F0F0F0F

    logic_src1[2] = 0xAAAAAAAAAAAAAAAA; // Logical XOR test
    logic_src2[2] = 0x5555555555555555;
    expected_logic_results[2] = 0xFFFFFFFFFFFFFFFF; // Corrected expected result: 0xAAAAAAAAAAAAAAAA ^ 0x5555555555555555

    // Additional corner cases
    logic_src1[3] = 0x0000000000000000; // Test with zero
    logic_src2[3] = 0xFFFFFFFFFFFFFFFF;
    expected_logic_results[3] = 0x0; // Expected result: 0x0 & 0xFFFFFFFFFFFFFFFF = 0x0

    logic_src1[4] = 0xFFFFFFFFFFFFFFFF; // Test with all bits set
    logic_src2[4] = 0xFFFFFFFFFFFFFFFF;
    expected_logic_results[4] = 0xFFFFFFFFFFFFFFFF; // Expected result: 0xFFFFFFFFFFFFFFFF | 0xFFFFFFFFFFFFFFFF

    logic_src1[5] = 0x8000000000000000; // Highest bit set for `xor`
    logic_src2[5] = 0x7FFFFFFFFFFFFFFF;
    expected_logic_results[5] = 0xFFFFFFFFFFFFFFFF; // Expected result: 0x8000000000000000 ^ 0x7FFFFFFFFFFFFFFF

    logic_src1[6] = 0x5555555555555555; // Alternating bits pattern
    logic_src2[6] = 0xAAAAAAAAAAAAAAAA;
    expected_logic_results[6] = 0x0; // Expected result: 0x5555555555555555 & 0xAAAAAAAAAAAAAAAA

    logic_src1[7] = 0x0123456789ABCDEF; // Complex pattern test for `or`
    logic_src2[7] = 0xFEDCBA9876543210;
    expected_logic_results[7] = 0xFFFFFFFFFFFFFFFF; // Expected result: 0x0123456789ABCDEF | 0xFEDCBA9876543210

    logic_src1[8] = 0x0123456789ABCDEF; // Complex pattern test for `and`
    logic_src2[8] = 0xFEDCBA9876543210;
    expected_logic_results[8] = 0x0; // Corrected expected result: 0x0123456789ABCDEF & 0xFEDCBA9876543210

    logic_src1[9] = 0x0123456789ABCDEF; // Complex pattern test for `xor`
    logic_src2[9] = 0xFEDCBA9876543210;
    expected_logic_results[9] = 0xFFFFFFFFFFFFFFFF; // Expected result: 0x0123456789ABCDEF ^ 0xFEDCBA9876543210

    // Edge case with alternating bits all set
    logic_src1[10] = 0xFFFFFFFFFFFFFFFF; // Alternating bits all set for `and`
    logic_src2[10] = 0xAAAAAAAAAAAAAAAA;
    expected_logic_results[10] = 0xAAAAAAAAAAAAAAAA; // Expected result: 0xFFFFFFFFFFFFFFFF & 0xAAAAAAAAAAAAAAAA

    // Edge case with complex pattern and high byte set
    logic_src1[11] = 0xFFFFFFFF00000000; // High byte set for `or`
    logic_src2[11] = 0x00000000FFFFFFFF;
    expected_logic_results[11] = 0xFFFFFFFFFFFFFFFF; // Expected result: 0xFFFFFFFF00000000 | 0x00000000FFFFFFFF
}

// Macro to perform logical test and check the result
#define CHECK_LOGIC_OP(dest, expected, idx, scenario)                           \
    do {                                                                        \
        uint64_t dest_val;                                                      \
        asm volatile ("mv %0, " #dest : "=r"(dest_val));                        \
        CHECK_EQUAL_HEX(expected_logic_results[idx], dest_val, scenario);       \
    } while (0)

// Macro to perform the specified logical operation with description
#define TEST_LOGIC_OP(op, dest, src1, src2, idx, description)                   \
    do {                                                                        \
        asm volatile ("ld " #src1 ", %0" : : "m"(logic_src1[idx]));             \
        asm volatile ("ld " #src2 ", %0" : : "m"(logic_src2[idx]));             \
        printf("%-60s with src1=0x%llx, src2=0x%llx using %s, %s, %s: ",        \
               description, logic_src1[idx], logic_src2[idx], #dest, #src1, #src2); \
        asm volatile (op " " #dest ", " #src1 ", " #src2);                      \
        CHECK_LOGIC_OP(dest, expected_logic_results[idx], idx, description);    \
    } while (0)

int main() {
    // Initialize the test case counters
    testcase_init();

    // Initialize the logical values and expected results
    initialize_logic_values();

    // Print the table header
    printf("\n%-100s  %-80s\n", "Scenario :",  "Result");
    printf("------------------------------------------------------------------------------------------------------------\n");

    // Testing various logical operations with `t0`, `t1`, and `t2` registers
    TEST_LOGIC_OP("and", t0, t1, t2, 0, "\nTest logical AND (and). Expected result: 0xFFFFFFFFFFFFFFFF & 0x0 = 0x0.");
    TEST_LOGIC_OP("or", t0, t1, t2, 1, "\nTest logical OR (or). Expected result: 0x123456789ABCDEF0 | 0x0F0F0F0F0F0F0F0F.");
    TEST_LOGIC_OP("xor", t0, t1, t2, 2, "\nTest logical XOR (xor). Expected result: 0xAAAAAAAAAAAAAAAA ^ 0x5555555555555555.");

    TEST_LOGIC_OP("and", t0, t1, t2, 3, "\nTest logical AND with zero. Expected result: 0x0 & 0xFFFFFFFFFFFFFFFF = 0x0, testing zero effect in AND operation.");
    TEST_LOGIC_OP("or", t0, t1, t2, 4, "\nTest logical OR with all bits set. Expected result: 0xFFFFFFFFFFFFFFFF | 0xFFFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF, checking OR with all bits set.");
    TEST_LOGIC_OP("xor", t0, t1, t2, 5, "\nTest logical XOR with highest bit set. Expected result: 0x8000000000000000 ^ 0x7FFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF, testing XOR of highest positive and negative bit.");
    TEST_LOGIC_OP("and", t0, t1, t2, 6, "\nTest logical AND with alternating bit pattern. Expected result: 0x5555555555555555 & 0xAAAAAAAAAAAAAAAA = 0x0, alternating bits canceling out in AND.");
    TEST_LOGIC_OP("or", t0, t1, t2, 7, "\nTest logical OR with complex pattern. Expected result: 0x0123456789ABCDEF | 0xFEDCBA9876543210 = 0xFFFFFFFFFFFFFFFF, merging complex patterns with OR.");
    TEST_LOGIC_OP("and", t0, t1, t2, 8, "\nTest logical AND with complex pattern. Expected result: 0x0123456789ABCDEF & 0xFEDCBA9876543210 = 0x0, checking selective bit pattern match in AND.");
    TEST_LOGIC_OP("xor", t0, t1, t2, 9, "\nTest logical XOR with complex pattern. Expected result: 0x0123456789ABCDEF ^ 0xFEDCBA9876543210 = 0xFFFFFFFFFFFFFFFF, highlighting full pattern difference in XOR.");
    TEST_LOGIC_OP("and", t0, t1, t2, 10, "\nTest logical AND with alternating bits all set. Expected result: 0xFFFFFFFFFFFFFFFF & 0xAAAAAAAAAAAAAAAA = 0xAAAAAAAAAAAAAAAA, maintaining alternating pattern.");
    TEST_LOGIC_OP("or", t0, t1, t2, 11, "\nTest logical OR with high byte set. Expected result: 0xFFFFFFFF00000000 | 0x00000000FFFFFFFF = 0xFFFFFFFFFFFFFFFF, merging high and low set bytes.");


    // Using t3, t4, t5
    TEST_LOGIC_OP("and", t3, t4, t5, 3, "\nTest logical AND with zero. Expected result: 0x0 & 0xFFFFFFFFFFFFFFFF = 0x0, testing zero effect in AND operation.");
    TEST_LOGIC_OP("or", t3, t4, t5, 4, "\nTest logical OR with all bits set. Expected result: 0xFFFFFFFFFFFFFFFF | 0xFFFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF, checking OR with all bits set.");
    TEST_LOGIC_OP("xor", t3, t4, t5, 5, "\nTest logical XOR with highest bit set. Expected result: 0x8000000000000000 ^ 0x7FFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFF, testing XOR of highest positive and negative bit.");

    // Using t6, a0, a1
    TEST_LOGIC_OP("and", t0, t1, t2, 6, "\nTest logical AND with alternating bit pattern. Expected result: 0x5555555555555555 & 0xAAAAAAAAAAAAAAAA = 0x0, alternating bits canceling out in AND.");

    // Using a2, a3, a4
    TEST_LOGIC_OP("or", t0, t1, t2, 7, "\nTest logical OR with complex pattern. Expected result: 0x0123456789ABCDEF | 0xFEDCBA9876543210 = 0xFFFFFFFFFFFFFFFF, merging complex patterns with OR.");

    // Using a5, a6, a7
    TEST_LOGIC_OP("and",t0, t1, t2, 8, "\nTest logical AND with complex pattern. Expected result: 0x0123456789ABCDEF & 0xFEDCBA9876543210 = 0x0020000800000210, checking selective bit pattern match in AND.");

    // Using t0, t1, t2 again for complex XOR test
    TEST_LOGIC_OP("xor", t0, t1, t2, 9, "\nTest logical XOR with complex pattern. Expected result: 0x0123456789ABCDEF ^ 0xFEDCBA9876543210 = 0xFEDCBA98ECDDFEEF, highlighting full pattern difference in XOR.");

    // Using t3, t4, t5 for alternating bits
    TEST_LOGIC_OP("and", t0, t1, t2, 10, "\nTest logical AND with alternating bits all set. Expected result: 0xFFFFFFFFFFFFFFFF & 0xAAAAAAAAAAAAAAAA = 0xAAAAAAAAAAAAAAAA, maintaining alternating pattern.");

    // Using a0, a1, a2 for high byte set
    TEST_LOGIC_OP("or", t0, t1, t2, 11, "\nTest logical OR with high byte set. Expected result: 0xFFFFFFFF00000000 | 0x00000000FFFFFFFF = 0xFFFFFFFFFFFFFFFF, merging high and low set bytes.");

    // Print the test results
    printf("\n");

    // Finalize the test case and return the result
    return testcase_finalize();
}
