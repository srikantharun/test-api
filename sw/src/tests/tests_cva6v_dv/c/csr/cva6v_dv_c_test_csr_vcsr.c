// test_vcsr.c
#include "common.h"

// Declare the assembly test function
//ASM extern void run_vector_assembly_tests();
//ASM extern volatile uint32_t asm_test_passed;// Function to test VCSR register
void test_vcsr() {
    printf("\n--- Testing VCSR Register ---\n");

    // Set VCSR
    uint32_t vcsr_value = (0 << 0) | (0b10 << 1); // VXSAT=0, VXRM=Round to Zero
    write_csr(vcsr, vcsr_value);

    // Read back VCSR
    uint32_t read_vcsr = read_csr(vcsr);

    // Verification
    CHECK_TRUE(read_vcsr == vcsr_value,
        "VCSR Test Failed: Expected VCSR=0x%02x, Got VCSR=0x%02x\n",
        vcsr_value, read_vcsr);

    if (read_vcsr == vcsr_value) {
        printf("VCSR Test Passed: VCSR=0x%02x\n", read_vcsr);
    } else {
        printf("VCSR Test Failed: Expected VCSR=0x%02x, Got VCSR=0x%02x\n",
            vcsr_value, read_vcsr);
    }
}

int main() {
    // Initialize the test case

    testcase_init();

    // Configure privilege and vector extension
    configure_privilege_and_vector_extension();

    // Initialize vector registers
    initialize_vector_registers();

    // Run the VCSR test
    test_vcsr();

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
        printf("\n*** VCSR TEST PASSED ***\n");
    } else {
        printf("\n*** VCSR TEST FAILED ***\n");
    }

    return test_result;
}
