// test_vstart.c
#include "common.h"

// Declare the assembly test function
//ASM extern void run_vector_assembly_tests();
//ASM extern volatile uint32_t asm_test_passed;

// Function prototypes
void test_vstart_initialization();
void test_vstart_reset_after_vector_instructions();
void test_vstart_non_zero_values();
void test_vstart_multiple_vector_instructions();
void test_vstart_boundary_conditions();

// Function to test VSTART register initialization
void test_vstart_initialization() {
    printf("\n--- Testing VSTART Initialization ---\n");

    // Read the VSTART register at initialization
    uint32_t vstart_init = read_csr(vstart);
    if (vstart_init != 0) {
        printf("VSTART Initialization Failed: Expected 0, Got %u\n", vstart_init);
        CHECK_TRUE(false, "VSTART Initialization Test Failed.\n");
    } else {
        printf("VSTART Initialization Passed: VSTART = 0\n");
    }
}

// Function to test that VSTART is reset after vector instructions
void test_vstart_reset_after_vector_instructions() {
    printf("\n--- Testing VSTART Reset After Vector Instructions ---\n");

    // Set VSTART to a non-zero value
    write_csr(vstart, 5);

    // Perform a vector instruction
    __asm__ volatile (
        "vsetvli t0, %0, e32, m1, tu, mu\n"  // Set vector configuration for 32-bit elements
        :
        : "r" (8)
        : "t0"
    );

    // Read VSTART after the instruction
    uint32_t vstart_after = read_csr(vstart);
    if (vstart_after != 0) {
        printf("VSTART Reset Failed: Expected 0, Got %u\n", vstart_after);
        CHECK_TRUE(false, "VSTART Reset Test Failed.\n");
    } else {
        printf("VSTART Reset Passed: VSTART = 0\n");
    }
}

// Function to test that setting VSTART to non-zero does not affect vector operations
void test_vstart_non_zero_values() {
    printf("\n--- Testing VSTART with Non-Zero Values ---\n");

    // Prepare test data
    uint32_t test_data[8] __attribute__((aligned(32))) = {10, 20, 30, 40, 50, 60, 70, 80};
    uint32_t result_data[8] __attribute__((aligned(32))) = {0};

    // Set VSTART to a non-zero value
    write_csr(vstart, 3);

    // Perform vector load/store operations
    __asm__ volatile (
        "vsetvli t0, %0, e32, m1, tu, mu\n"  // Set vector configuration for 32-bit elements
        "vle32.v v1, (%1)\n"                 // Load 32-bit elements into v1
        "vse32.v v1, (%2)\n"                 // Store from v1 to result_data
        :
        : "r" (8), "r" (test_data), "r" (result_data)
        : "t0", "memory", "v1"
    );

    // Read the VSTART register to verify it has been reset to zero
    uint32_t vstart_after = read_csr(vstart);
    if (vstart_after != 0) {
        printf("VSTART Reset Failed: Expected 0, Got %u\n", vstart_after);
        CHECK_TRUE(false, "VSTART Reset After Non-Zero Test Failed.\n");
    } else {
        printf("VSTART Reset Passed After Non-Zero Value: VSTART = 0\n");
    }

    // Check results to ensure all elements are processed normally
    bool test_passed = true;
    for (int i = 0; i < 8; i++) {
        uint32_t expected = test_data[i];  // Expect all elements to be copied
        if (result_data[i] != expected) {
            test_passed = false;
            printf("VSTART Non-Zero Effect Test Failed at index %d: Expected %u, Got %u\n", i, expected, result_data[i]);
        }
    }

    if (test_passed) {
        printf("VSTART Non-Zero Effect Test Passed: All elements correctly processed.\n");
    }
    CHECK_TRUE(test_passed, "VSTART Non-Zero Effect Test Failed.\n");
}

// Function to test multiple vector instructions and VSTART reset
void test_vstart_multiple_vector_instructions() {
    printf("\n--- Testing VSTART Reset with Multiple Vector Instructions ---\n");

    // Prepare test data
    uint32_t test_data1[4] __attribute__((aligned(32))) = {100, 200, 300, 400};
    uint32_t result_data1[4] __attribute__((aligned(32))) = {0};

    uint32_t test_data2[4] __attribute__((aligned(32))) = {500, 600, 700, 800};
    uint32_t result_data2[4] __attribute__((aligned(32))) = {0};

    // Set VSTART to a non-zero value
    write_csr(vstart, 2);

    // Perform first vector load/store
    __asm__ volatile (
        "vsetvli t1, %0, e32, m1, tu, mu\n"  // Set vector configuration for 32-bit elements
        "vle32.v v2, (%1)\n"                 // Load 32-bit elements into v2
        "vse32.v v2, (%2)\n"                 // Store from v2 to result_data1
        :
        : "r" (4), "r" (test_data1), "r" (result_data1)
        : "t1", "memory", "v2"
    );

    // Perform second vector load/store
    __asm__ volatile (
        "vsetvli t1, %0, e32, m1, tu, mu\n"  // Reset VSTART via another vector instruction
        "vle32.v v3, (%1)\n"                 // Load 32-bit elements into v3
        "vse32.v v3, (%2)\n"                 // Store from v3 to result_data2
        :
        : "r" (4), "r" (test_data2), "r" (result_data2)
        : "t1", "memory", "v3"
    );

    // Read the VSTART register to verify it has been reset to zero
    uint32_t vstart_after = read_csr(vstart);
    if (vstart_after != 0) {
        printf("VSTART Reset Failed After Multiple Instructions: Expected 0, Got %u\n", vstart_after);
        CHECK_TRUE(false, "VSTART Multiple Instructions Reset Test Failed.\n");
    } else {
        printf("VSTART Reset Passed After Multiple Instructions: VSTART = 0\n");
    }

    // Check first result set
    bool test_passed = true;
    for (int i = 0; i < 4; i++) {
        uint32_t expected = test_data1[i];
        if (result_data1[i] != expected) {
            test_passed = false;
            printf("VSTART Multiple Instructions Test Failed at first set index %d: Expected %u, Got %u\n", i, expected, result_data1[i]);
        }
    }

    // Check second result set
    for (int i = 0; i < 4; i++) {
        uint32_t expected = test_data2[i];
        if (result_data2[i] != expected) {
            test_passed = false;
            printf("VSTART Multiple Instructions Test Failed at second set index %d: Expected %u, Got %u\n", i, expected, result_data2[i]);
        }
    }

    if (test_passed) {
        printf("VSTART Multiple Instructions Test Passed: All elements correctly processed.\n");
    }
    CHECK_TRUE(test_passed, "VSTART Multiple Instructions Test Failed.\n");
}

// Function to test VSTART boundary conditions
void test_vstart_boundary_conditions() {
    printf("\n--- Testing VSTART Boundary Conditions ---\n");

    // Test VSTART set to 0 (should have no effect)
    write_csr(vstart, 0);
    uint32_t test_data0[4] __attribute__((aligned(32))) = {1, 2, 3, 4};
    uint32_t result_data0[4] __attribute__((aligned(32))) = {0};

    __asm__ volatile (
        "vsetvli t2, %0, e32, m1, tu, mu\n"
        "vle32.v v4, (%1)\n"
        "vse32.v v4, (%2)\n"
        :
        : "r" (4), "r" (test_data0), "r" (result_data0)
        : "t2", "memory", "v4"
    );

    uint32_t vstart_after0 = read_csr(vstart);
    if (vstart_after0 != 0) {
        printf("VSTART Reset Failed After Boundary Test (VSTART=0): Expected 0, Got %u\n", vstart_after0);
        CHECK_TRUE(false, "VSTART Boundary Test Failed for VSTART=0.\n");
    } else {
        printf("VSTART Reset Passed After Boundary Test (VSTART=0): VSTART = 0\n");
    }

    bool test_passed0 = true;
    for (int i = 0; i < 4; i++) {
        uint32_t expected = test_data0[i];
        if (result_data0[i] != expected) {
            test_passed0 = false;
            printf("VSTART Boundary Test Failed at VSTART=0 index %d: Expected %u, Got %u\n", i, expected, result_data0[i]);
        }
    }

    if (test_passed0) {
        printf("VSTART Boundary Test Passed for VSTART=0: All elements correctly processed.\n");
    }
    CHECK_TRUE(test_passed0, "VSTART Boundary Test Failed for VSTART=0.\n");

    // Test VSTART set to maximum value (assuming 31 for a 5-bit field; adjust as per actual spec)
    #define VSTART_MAX 31
    write_csr(vstart, VSTART_MAX);
    uint32_t test_data_max[4] __attribute__((aligned(32))) = {5, 6, 7, 8};
    uint32_t result_data_max[4] __attribute__((aligned(32))) = {0};

    __asm__ volatile (
        "vsetvli t3, %0, e32, m1, tu, mu\n"
        "vle32.v v5, (%1)\n"
        "vse32.v v5, (%2)\n"
        :
        : "r" (4), "r" (test_data_max), "r" (result_data_max)
        : "t3", "memory", "v5"
    );

    uint32_t vstart_after_max = read_csr(vstart);
    if (vstart_after_max != 0) {
        printf("VSTART Reset Failed After Boundary Test (VSTART=MAX): Expected 0, Got %u\n", vstart_after_max);
        CHECK_TRUE(false, "VSTART Boundary Test Failed for VSTART=MAX.\n");
    } else {
        printf("VSTART Reset Passed After Boundary Test (VSTART=MAX): VSTART = 0\n");
    }

    bool test_passed_max = true;
    for (int i = 0; i < 4; i++) {
        uint32_t expected = test_data_max[i];
        if (result_data_max[i] != expected) {
            test_passed_max = false;
            printf("VSTART Boundary Test Failed at VSTART=MAX index %d: Expected %u, Got %u\n", i, expected, result_data_max[i]);
        }
    }

    if (test_passed_max) {
        printf("VSTART Boundary Test Passed for VSTART=MAX: All elements correctly processed.\n");
    }
    CHECK_TRUE(test_passed_max, "VSTART Boundary Test Failed for VSTART=MAX.\n");
}

// Main VSTART Test Function
void test_vstart() {
    printf("\n=== Starting Comprehensive VSTART Register Tests ===\n");

    // Run individual test cases
    test_vstart_initialization();
    test_vstart_reset_after_vector_instructions();
    test_vstart_non_zero_values();
    test_vstart_multiple_vector_instructions();
    test_vstart_boundary_conditions();

    printf("\n=== VSTART Register Tests Completed ===\n");
}

int main() {
    // Initialize the test case
    testcase_init();
    // Configure privilege and vector extension
    configure_privilege_and_vector_extension();

    // Initialize vector registers
    initialize_vector_registers();

    // Run the comprehensive VSTART test
    test_vstart();

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
        printf("\n*** VSTART TESTS PASSED ***\n");
    } else {
        printf("\n*** VSTART TESTS FAILED ***\n");
    }

    return test_result;
}
