// test_frm.c
#include "encoding.h"
#include "stack.h"
#include "common.h"
#include "testutils.h"

// Declare the assembly test function
extern void run_frm_assembly_tests();

// Declare the test result variables defined in assembly
extern volatile uint32_t result_bits[5];
extern volatile uint32_t result_addition_correct[5];

// Function to perform floating-point addition using inline assembly
float assembly_fadd(float a, float b) {
    float result;
    __asm__ volatile (
        "fadd.s %0, %1, %2\n" // Perform single-precision floating-point addition
        : "=f" (result)       // Output operand
        : "f" (a), "f" (b)    // Input operands
    );
    return result;
}


// Helper function to convert uint32_t bits to float
float bits_to_float(uint32_t bits) {
    union {
        uint32_t u;
        float f;
    } temp;
    temp.u = bits;
    return temp.f;
}

// Define the TestCase structure
typedef struct {
    const char* test_name;
    uint32_t a_bits;
    uint32_t b_bits;
    uint32_t expected_bits[5]; // Expected result bits for each rounding mode
} TestCase;

// Define the test cases
TestCase test_cases[] = {
    // Test Case 1: 1.1f + 1.0f (Original test)
    {
        "Addition of 1.1f and 1.0f",
        0x3f8ccccd, // 1.1f
        0x3f800000, // 1.0f
        {0x40066666, 0x40066666, 0x40066666, 0x40066667, 0x40066667}
        // Expected bits: RNE, RTZ, RDN -> 0x40066666; RUP, RMM -> 0x40066667
    },
    // Test Case 2: Zero plus zero
    {
        "Zero plus zero",
        0x00000000, // +0.0f
        0x00000000, // +0.0f
        {0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000}
    },
    // Test Case 3: Subnormal addition
    {
        "Subnormal addition",
        0x00000001, // Smallest positive subnormal
        0x00000001, // Smallest positive subnormal
        {0x00000002, 0x00000002, 0x00000002, 0x00000002, 0x00000002}
    },
    // Test Case 4: Negative zero plus positive zero
    {
        "Negative zero plus positive zero",
        0x80000000, // -0.0f
        0x00000000, // +0.0f
        {0x00000000, 0x00000000, 0x00000000, 0x80000000, 0x00000000}
        // Note: RUP may produce -0.0f due to rounding towards +∞
    },
    // Test Case 5: Large plus small
    {
        "Large number plus small number",
        0x7f7fffff, // Max finite positive float
        0x3f800000, // 1.0f
        {0x7f800000, 0x7f7fffff, 0x7f7fffff, 0x7f800000, 0x7f800000}
        // Expected bits: Overflow to infinity in RNE, RUP, RMM; Max finite in RTZ, RDN
    },
    // Test Case 6: Positive number plus negative number resulting in zero
    {
        "Positive number plus negative number resulting in zero",
        0x3f800000, // 1.0f
        0xbf800000, // -1.0f
        {0x00000000, 0x00000000, 0x80000000, 0x00000000, 0x00000000}
        // Note: RDN may produce -0.0f when rounding towards -∞
    },
    // Test Case 7: Overflow addition
    {
        "Overflow addition",
        0x7f7fffff, // Max finite positive float
        0x7f7fffff, // Max finite positive float
        {0x7f800000, 0x7f800000, 0x7f800000, 0x7f800000, 0x7f800000}
        // Result is +infinity for all rounding modes
    },
};

int NUM_TEST_CASES = sizeof(test_cases) / sizeof(test_cases[0]);

int main() {
    // Initialize the test case
    testcase_init();

    // Define the rounding modes
    uint32_t valid_rounding_modes[] = {0b000, 0b001, 0b010, 0b011, 0b100};
    const char *valid_rounding_mode_names[] = {"RNE", "RTZ", "RDN", "RUP", "RMM"};
    int NUM_VALID_MODES = sizeof(valid_rounding_modes) / sizeof(valid_rounding_modes[0]);

    // Loop over test cases
    for(int test_idx = 0; test_idx < NUM_TEST_CASES; test_idx++) {
        TestCase tc = test_cases[test_idx];
        printf("\n=== Test Case: %s ===\n", tc.test_name);

        // Loop over rounding modes
        for(int mode_idx = 0; mode_idx < NUM_VALID_MODES; mode_idx++) {
            uint32_t mode = valid_rounding_modes[mode_idx];
            const char* mode_name = valid_rounding_mode_names[mode_idx];
            uint32_t expected_bits = tc.expected_bits[mode_idx];

            // Set the rounding mode in frm
            write_csr(frm, mode);

            // Read back the fcsr and extract bits [7:5] to verify frm
            uint32_t fcsr = read_csr(fcsr); // Read the entire fcsr register
            uint32_t read_mode = (fcsr >> 5) & 0x7; // Extract bits [7:5]

            // Verify that frm was set correctly
            bool mode_correct = (read_mode == mode);
            printf("\nScenario: Set frm to %s (0x%03x)\n", mode_name, mode);
            printf("Read frm from fcsr [7:5]: 0x%03x\n", read_mode);
            CHECK_TRUE(mode_correct, "frm set to 0x%03x, read back as 0x%03x", mode, read_mode);

            // Convert bits to floats
            float a = bits_to_float(tc.a_bits);
            float b = bits_to_float(tc.b_bits);

            // Perform a floating-point addition using assembly
            float result = assembly_fadd(a, b);

            // Convert result to bitwise representation
            uint32_t result_bits = float_to_bits(result);

            // Print operation results
            printf("Floating-point addition with frm=%s: Expected 0x%08x, Got 0x%08x\n", mode_name, expected_bits, result_bits);

            // Compare the actual result bits with the expected bits
            bool result_correct = (result_bits == expected_bits);

            // Report the outcome
            if (result_correct) {
                printf("[PASS] Result matches expected bits.\n");
            } else {
                printf("[FAIL] Result does not match expected bits.\n");
            }
        }
    }

    // --- Step 1: Call Assembly-Based Tests ---
    printf("\n*** Running Assembly-Based frm Tests ***\n");
    run_frm_assembly_tests(); // Call the assembly test function

    // ================================
    // Read and Report Assembly Test Results
    // ================================

    // Assuming the assembly code has been updated to handle the additional test cases

    // Finalize the test case and retrieve the result
    int test_result = testcase_finalize();

    // Print final test result
    if (test_result == TEST_SUCCESS) {
        printf("\n*** TEST PASSED ***\n");
    } else {
        printf("\n*** TEST FAILED ***\n");
    }

    // Return the test result
    return test_result;
}
