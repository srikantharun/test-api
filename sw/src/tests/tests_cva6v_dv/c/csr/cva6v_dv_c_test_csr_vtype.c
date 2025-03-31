// test_vl_vtype.c
#include "common.h"
// Declare the assembly test function
//ASM extern void run_vector_assembly_tests();
//ASM extern volatile uint32_t asm_test_passed;

// Function to test VL and VTYPE registers
void test_vl_vtype() {
    printf("\n--- Testing VL and VTYPE Registers ---\n");

    // Desired configuration
    uint64_t desired_vl = 8;
    uint32_t vsetvli_imm = VSETVLI_IMM; // e32, m1

    // Set VL and VTYPE using vsetvli
    asm volatile(
        "vsetvli x0, %0, %1"   // x0 is rd (ignored), rs1 = desired_vl, imm = vsetvli_imm
        :
        : "r" (desired_vl), "i" (vsetvli_imm)
        : "v0" // Clobber list: indicates that vector registers are modified
    );

    // Read back VL and VTYPE
    uint64_t read_vl;
    uint64_t read_vtype;

    // Read VL
    asm volatile(
        "csrr %0, vl"          // Read vl CSR into read_vl
        : "=r" (read_vl)
        :
        :
    );

    // Read VTYPE
    asm volatile(
        "csrr %0, vtype"       // Read vtype CSR into read_vtype
        : "=r" (read_vtype)
        :
        :
    );

    // Expected VTYPE encoding
    // SEW=32 (e32) -> 2
    // LMUL=1 (m1) -> 0
    uint64_t expected_vtype = 0x2;

    // Verification
    CHECK_TRUE(read_vl == desired_vl && read_vtype == expected_vtype,
        "VL and VTYPE Test Failed: Expected VL=%lu, VTYPE=0x%lx; Got VL=%lu, VTYPE=0x%lx\n",
        desired_vl, expected_vtype, read_vl, read_vtype);

    if (read_vl == desired_vl && read_vtype == expected_vtype) {
        printf("VL and VTYPE Test Passed: VL=%lu, VTYPE=0x%lx\n", read_vl, read_vtype);
    } else {
        printf("VL and VTYPE Test Failed: Expected VL=%lu, VTYPE=0x%lx; Got VL=%lu, VTYPE=0x%lx\n",
            desired_vl, expected_vtype, read_vl, read_vtype);
    }
}

int main() {
    // Initialize the test case
    testcase_init();

    // Configure privilege and vector extension
    configure_privilege_and_vector_extension();

    // Initialize vector registers
    initialize_vector_registers();

    // Run the VL and VTYPE test
    test_vl_vtype();

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
        printf("\n*** VL and VTYPE TEST PASSED ***\n");
    } else {
        printf("\n*** VL and VTYPE TEST FAILED ***\n");
    }

    return test_result;
}
