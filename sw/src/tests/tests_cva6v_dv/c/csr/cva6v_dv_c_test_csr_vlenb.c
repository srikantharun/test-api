// test_vlenb.c
#include "common.h"

// Declare the assembly test function
//ASM extern void run_vector_assembly_tests();
//ASM extern volatile uint32_t asm_test_passed;
// Function to test VLENB register
void test_vlenb() {
    printf("\n--- Testing VLENB Register ---\n");

    uint32_t vlenb = read_csr(vlenb);
    printf("VLENB (Vector Register Length in Bytes): %u\n", vlenb);

    CHECK_TRUE((vlenb > 0),
        "VLENB Test Failed: VLENB should be greater than 0. Got VLENB=%u\n", vlenb);

    if (vlenb > 0) {
        printf("VLENB Test Passed: VLENB=%u\n", vlenb);
    } else {
        printf("VLENB Test Failed: VLENB should be greater than 0. Got VLENB=%u\n", vlenb);
    }
}

int main() {
    // Initialize the test case
    testcase_init();

    // Configure privilege and vector extension
    configure_privilege_and_vector_extension();

    // Initialize vector registers
    initialize_vector_registers();

    // Run the VLENB test
    test_vlenb();

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
        printf("\n*** VLENB TEST PASSED ***\n");
    } else {
        printf("\n*** VLENB TEST FAILED ***\n");
    }

    return test_result;
}
