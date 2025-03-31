// test_vxsat_vxrm.c
#include "common.h"
// Declare the assembly test function
//ASM extern void run_vector_assembly_tests();
//ASM extern volatile uint32_t asm_test_passed;

// Function to test VXSAT and VXRM registers
void test_vxsat_vxrm() {
    printf("\n--- Testing VXSAT and VXRM Registers ---\n");

    // Clear VXSAT
    write_csr(vxsat, 0);

    // Set VXRM to Round-to-Nearest-Up (0b00)
    write_csr(vxrm, 0b00);

    // Prepare test data
    uint32_t src_data[8] __attribute__((aligned(32))) = {0x7FFFFFFF, 1, 2, 3, 4, 5, 6, 7};
    uint32_t result_data[8] __attribute__((aligned(32))) = {0};

    // Perform vector saturating addition
    __asm__ volatile (
        "vsetvli t0, %0, e32, m1, tu, mu\n"  // Set vector configuration for 32-bit elements
        "vle32.v v0, (%1)\n"                 // Load vector
        "addi t1, x0, 1\n"
        "vsadd.vx v1, v0, t1\n"              // Saturating addition
        "vse32.v v1, (%2)\n"                 // Store result
        :
        : "r" (8), "r" (src_data), "r" (result_data)
        : "t0", "t1", "memory", "v0", "v1"
    );

    // Check VXSAT
    uint32_t vxsat = read_csr(vxsat);
    if (vxsat == 1) {
        printf("VXSAT Test Passed: Saturation occurred as expected.\n");
    } else {
        printf("VXSAT Test Failed: Expected VXSAT=1, Got VXSAT=%u\n", vxsat);
    }

    // Check results
    CHECK_TRUE(result_data[0] == 0x7FFFFFFF, "Result incorrectly saturated: Expected 0x7FFFFFFF, Got 0x%08x\n", result_data[0]);
    if (result_data[0] == 0x7FFFFFFF) {
        printf("Result correctly saturated to maximum positive value.\n");
    } else {
        printf("Result incorrect: Expected 0x7FFFFFFF, Got 0x%08x\n", result_data[0]);
    }
}

int main() {
    // Initialize the test case
    testcase_init();

    // Configure privilege and vector extension
    configure_privilege_and_vector_extension();

    // Initialize vector registers
    initialize_vector_registers();

    // Run the VXSAT and VXRM test
    test_vxsat_vxrm();

    // Finalize the test case and retrieve the result
    int test_result = testcase_finalize();

    // --- Call Assembly-Based Tests ---
    //ASM printf("\n*** Running Assembly-Based Vector Register Tests ***\n");
    //ASM run_vector_assembly_tests(); // Uncomment this to run assembly tests

    //ASM // Check assembly test results
    //ASM if (asm_test_passed) {
    //ASM     printf("Assembly Vector Register Tests Passed.\n");
    //ASM } else {
    //ASM     printf("Assembly Vector Register Tests Failed.\n");
    //ASM }

    // Print final test result
    if (test_result == 0) {
        printf("\n*** VXSAT and VXRM TEST PASSED ***\n");
    } else {
        printf("\n*** VXSAT and VXRM TEST FAILED ***\n");
    }

    return test_result;
}
