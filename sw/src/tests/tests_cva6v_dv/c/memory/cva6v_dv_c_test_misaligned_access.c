// main.c
#include <stdint.h>
#include <stdbool.h>
#include "encoding.h"
#include <printf.h>
// #include "common.h"
#include "testutils.h"

// Define test masks with descriptive names
#define TEST_ALIGNED_INSTR_FETCH             (1 << 0)
#define TEST_MISALIGNED_INSTR_FETCH          (1 << 1)
#define TEST_ALIGNED_LOAD_STORE_BYTE         (1 << 2)
#define TEST_MISALIGNED_LOAD_STORE_BYTE      (1 << 3)
#define TEST_ALIGNED_LOAD_STORE_HALFWORD     (1 << 4)
#define TEST_MISALIGNED_LOAD_STORE_HALFWORD  (1 << 5)
#define TEST_ALIGNED_LOAD_STORE_WORD         (1 << 6)
#define TEST_MISALIGNED_LOAD_STORE_WORD      (1 << 7)
#define TEST_ALIGNED_LOAD_STORE_DWORD        (1 << 8)
#define TEST_MISALIGNED_LOAD_STORE_DWORD     (1 << 9)
#define TEST_MISALIGNED_AMO                  (1 << 10)
#define TEST_MISALIGNED_LR_SC                (1 << 11)
#define TEST_MISALIGNED_VECTOR_LOAD_STORE    (1 << 12)
#define TEST_MISALIGNED_FP_LOAD_STORE        (1 << 13)
#define TEST_MISALIGNED_PAGE_BOUNDARY_ACCESS (1 << 14)
#define TEST_MISALIGNED_CACHE_LINE_BOUNDARY  (1 << 15)
#define TEST_COMPRESSED_INSTR_C_EXTENSION    (1 << 16)
#define TEST_MISALIGNED_JUMP_C_EXTENSION     (1 << 17)
#define TEST_FENCES_AND_MISALIGNED_ACCESSES  (1 << 18)
#define TEST_MISALIGNED_AMO_ZAM_EXTENSION    (1 << 19)
#define TEST_MISALIGNED_VECTOR_WHOLE_REG     (1 << 20)

#define TEST_ALL  0x1FFFFF  // 21 bits for all tests 0 to 20

// Declare the assembly test function
extern void run_misaligned_access_tests(uint32_t test_mask);
extern void reset_registers();

// Declare the result variables defined in assembly

extern volatile uint64_t result_misaligned_vl1r[8];
extern volatile uint32_t result_misaligned_lh;
extern volatile uint32_t result_misaligned_lw;
extern volatile uint64_t result_misaligned_ld;
extern volatile uint32_t result_misaligned_amo;
extern volatile uint32_t result_misaligned_lrsc;
extern volatile uint32_t result_misaligned_vl[8];
extern volatile uint32_t result_misaligned_flw;
extern volatile uint32_t result_misaligned_amo_zam;
extern volatile uint64_t result_misaligned_vl1r[8];

// Declare flags to indicate which traps occurred
volatile bool trap_misaligned_fetch = false;
volatile bool trap_fetch_access = false;
volatile bool trap_illegal_instruction = false;
volatile bool trap_breakpoint = false;
volatile bool trap_misaligned_load = false;
volatile bool trap_load_access = false;
volatile bool trap_misaligned_store = false;
volatile bool trap_store_access = false;
volatile bool trap_user_ecall = false;
volatile bool trap_supervisor_ecall = false;
volatile bool trap_machine_ecall = false;
volatile bool trap_fetch_page_fault = false;
volatile bool trap_load_page_fault = false;
volatile bool trap_store_page_fault = false;
// Add more flags as needed for other exception c
// Declare flags to indicate which traps occurred
volatile bool trap_misaligned_instruction_fetch = false;
volatile bool trap_misaligned_amo = false;
volatile bool trap_misaligned_lrsc = false;
volatile bool trap_misaligned_vector = false;
volatile bool trap_misaligned_fp = false;

// Variable to track overall test success
bool all_tests_passed = true;

// Function to print test result
void print_test_result(bool condition, const char* message) {
    if (condition) {
        printf("PASSED: %s\n", message);
    } else {
        printf("FAILED: %s\n", message);
        all_tests_passed = false;
    }
}


int main() {
    // Run all tests
    uint32_t test_mask = TEST_ALL;
    // Alternatively, run specific tests
    //uint32_t test_mask = TEST_MISALIGNED_VECTOR_LOAD_STORE;
    //uint32_t test_mask = TEST_ALIGNED_INSTR_FETCH | TEST_MISALIGNED_AMO;

    // Run the assembly tests with the specified test mask
    run_misaligned_access_tests(test_mask);

    reset_registers();
    return 0;
}


/*
int main() {
    // Initialize the test case
    testcase_init();

    // Set up the trap handler
    // setup_trap_handler();
    // Flags to indicate if misaligned accesses are supported
    bool misaligned_access_supported = false; // Set based on the processor's capability
    bool misaligned_amo_supported = false;    // Check if Zam extension is implemented
    bool compressed_extension = false;        // Check if C extension is implemented|

    // Read misa CSR to determine supported extensions
    uint64_t misa = read_csr(misa);
    if (misa & (1L << ('A' - 'A'))) {
        printf("Atomic extension (A) is supported.\n");
    }
    if (misa & (1L << ('C' - 'A'))) {
        compressed_extension = true;
        printf("Compressed extension (C) is supported.\n");
    }
    if (misa & (1L << ('M' - 'A'))) {
        printf("Integer Multiply/Divide extension (M) is supported.\n");
    }
    if (misa & (1L << ('F' - 'A'))) {
        printf("Single-Precision Floating-Point extension (F) is supported.\n");
    }
    if (misa & (1L << ('D' - 'A'))) {
        printf("Double-Precision Floating-Point extension (D) is supported.\n");
    }
    if (misa & (1L << ('V' - 'A'))) {
        printf("Vector extension (V) is supported.\n");
    }

    // Run the assembly tests
    run_misaligned_access_tests();

    // Note: The 'Z' extension is represented differently; adjust as needed.

    // Check Test Case 1: Aligned Instruction Fetch
    printf("\nTest Case 1: Aligned Instruction Fetch\n");
    print_test_result(!trap_misaligned_instruction_fetch, "No exception should occur for aligned instruction fetch");

    // Check Test Case 2: Misaligned Instruction Fetch
    printf("\nTest Case 2: Misaligned Instruction Fetch\n");
    if (compressed_extension) {
        print_test_result(!trap_misaligned_instruction_fetch, "No exception should occur if IALIGN=16");
    } else {
        print_test_result(trap_misaligned_instruction_fetch, "Exception should occur for misaligned instruction fetch");
    }

    // Check Test Case 4: Misaligned Load/Store Byte
    printf("\nTest Case 4: Misaligned Load/Store Byte\n");
    // Byte accesses are allowed at any alignment
    print_test_result(!trap_misaligned_load, "No exception should occur for misaligned byte load");
    print_test_result(!trap_misaligned_store, "No exception should occur for misaligned byte store");

    // Check Test Case 6: Misaligned Load/Store Half-Word
    printf("\nTest Case 6: Misaligned Load/Store Half-Word\n");
    if (trap_misaligned_load || trap_misaligned_store) {
        printf("PASSED: Misaligned half-word access caused a trap as expected.\n");
    } else {
        printf("FAILED: Misaligned half-word access did not cause a trap.\n");
        all_tests_passed = false;
    }

    // Check Test Case 8: Misaligned Load/Store Word
    printf("\nTest Case 8: Misaligned Load/Store Word\n");
    if (trap_misaligned_load || trap_misaligned_store) {
        printf("PASSED: Misaligned word access caused a trap as expected.\n");
    } else {
        printf("FAILED: Misaligned word access did not cause a trap.\n");
        all_tests_passed = false;
    }

    // Check Test Case 10: Misaligned Load/Store Double-Word
    printf("\nTest Case 10: Misaligned Load/Store Double-Word\n");
    if (trap_misaligned_load || trap_misaligned_store) {
        printf("PASSED: Misaligned double-word access caused a trap as expected.\n");
    } else {
        printf("FAILED: Misaligned double-word access did not cause a trap.\n");
        all_tests_passed = false;
    }

    // Check Test Case 11: Misaligned Atomic Operation (AMO)
    printf("\nTest Case 11: Misaligned Atomic Operation (AMO)\n");
    if (trap_misaligned_amo) {
        printf("PASSED: Misaligned AMO caused a trap as expected.\n");
    } else {
        if (misaligned_amo_supported) {
            printf("PASSED: Misaligned AMO succeeded as Zam extension is implemented.\n");
            // Check result if necessary
        } else {
            printf("FAILED: Misaligned AMO did not cause a trap but should have.\n");
            all_tests_passed = false;
        }
    }

    // Check Test Case 12: Misaligned LR/SC Sequence
    printf("\nTest Case 12: Misaligned LR/SC Sequence\n");
    if (trap_misaligned_lrsc) {
        printf("PASSED: Misaligned LR/SC caused a trap as expected.\n");
    } else {
        // SC returns 0 if successful, 1 if failed
        if (result_misaligned_lrsc == 0) {
            printf("FAILED: Misaligned LR/SC succeeded unexpectedly.\n");
            all_tests_passed = false;
        } else {
            printf("PASSED: Misaligned LR/SC failed as expected.\n");
        }
    }

    // Check Test Case 13: Misaligned Vector Load/Store
    printf("\nTest Case 13: Misaligned Vector Load/Store\n");
    if (trap_misaligned_vector) {
        printf("PASSED: Misaligned vector access caused a trap as expected.\n");
    } else {
        if (misaligned_access_supported) {
            printf("PASSED: Misaligned vector access succeeded as misaligned accesses are supported.\n");
            // Check result if necessary
        } else {
            printf("FAILED: Misaligned vector access did not cause a trap but should have.\n");
            all_tests_passed = false;
        }
    }

    // Check Test Case 14: Misaligned Floating-Point Load/Store
    printf("\nTest Case 14: Misaligned Floating-Point Load/Store\n");
    if (trap_misaligned_fp) {
        printf("PASSED: Misaligned floating-point access caused a trap as expected.\n");
    } else {
        if (misaligned_access_supported) {
            printf("PASSED: Misaligned floating-point access succeeded as misaligned accesses are supported.\n");
            // Check result if necessary
        } else {
            printf("FAILED: Misaligned floating-point access did not cause a trap but should have.\n");
            all_tests_passed = false;
        }
    }

    // Check Test Case 17: Compressed Instructions (C Extension)
    printf("\nTest Case 17: Compressed Instructions (C Extension)\n");
    if (compressed_extension) {
        print_test_result(!trap_misaligned_instruction_fetch, "Compressed instruction should execute without exception");
    } else {
        print_test_result(trap_misaligned_instruction_fetch, "Exception should occur for misaligned instruction fetch");
    }

    // Check Test Case 20: Misaligned AMO with Zam Extension
    printf("\nTest Case 20: Misaligned AMO with Zam Extension\n");
    if (misaligned_amo_supported) {
        // Check result of AMO operation
        uint32_t expected_value = 0x00000000; // Adjust based on expected result
        if (result_misaligned_amo_zam == expected_value) {
            printf("PASSED: Misaligned AMO with Zam extension succeeded and returned expected value.\n");
        } else {
            printf("FAILED: Misaligned AMO with Zam extension returned unexpected value.\n");
            all_tests_passed = false;
        }
    } else {
        if (trap_misaligned_amo) {
            printf("PASSED: Misaligned AMO caused a trap as expected.\n");
        } else {
            printf("FAILED: Misaligned AMO did not cause a trap but should have.\n");
            all_tests_passed = false;
        }
    }


    // Finalize the test case and retrieve the result
    int test_result = testcase_finalize();

    // Print final test result
    if (all_tests_passed && test_result == TEST_SUCCESS) {
        printf("\n*** ALL TESTS PASSED ***\n");
    } else {
        printf("\n*** SOME TESTS FAILED ***\n");
    }

    return all_tests_passed ? 0 : 1;
}
*/
