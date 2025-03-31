#include "common.h"
#include "testutils.h"

// Ensure the variables are aligned to 8 bytes for 64-bit atomic operations
#define ALIGN8 __attribute__((aligned(8)))

// Shared memory variables for atomic operations
volatile ALIGN8 uint64_t shared_var = 0;

// Structure to hold test results
typedef struct {
    const char *scenario;
    uint64_t dest_val;
    uint64_t expected_val;
    bool pass;
} TestResult;

// Array to store test results
#define NUM_TESTS 10
TestResult test_results[NUM_TESTS];
int current_test = 0;

// Helper functions to perform atomic operations using inline assembly

// Atomic Swap
uint64_t do_atomic_swap(volatile uint64_t *addr, uint64_t new_val) {
    uint64_t old_val;
    asm volatile (
        "amoswap.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (new_val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic Add
uint64_t do_atomic_add(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amoadd.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic XOR
uint64_t do_atomic_xor(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amoxor.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic OR
uint64_t do_atomic_or(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amoor.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic AND
uint64_t do_atomic_and(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amoand.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic Minimum
uint64_t do_atomic_min(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amomin.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic Maximum
uint64_t do_atomic_max(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amomax.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic Minimum Unsigned
uint64_t do_atomic_minu(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amominu.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Atomic Maximum Unsigned
uint64_t do_atomic_maxu(volatile uint64_t *addr, uint64_t val) {
    uint64_t old_val;
    asm volatile (
        "amomaxu.d %0, %1, (%2)"
        : "=&r" (old_val)
        : "r" (val), "r" (addr)
        : "memory"
    );
    return old_val;
}

// Test function prototypes
void test_amoswap_d();
void test_amoadd_d();
void test_amoxor_d();
void test_amoor_d();
void test_amoand_d();
void test_amomin_d();
void test_amomax_d();
void test_amominu_d();
void test_amomaxu_d();
void test_lr_sc_d();

// Utility function to reset shared variables before each test
void reset_shared_vars() {
    shared_var = 0;
}

// Function to add a test result
void add_test_result(const char *scenario, uint64_t dest_val, uint64_t expected_val, bool pass) {
    if (current_test < NUM_TESTS) {
        test_results[current_test].scenario = scenario;
        test_results[current_test].dest_val = dest_val;
        test_results[current_test].expected_val = expected_val;
        test_results[current_test].pass = pass;
        current_test++;
    }
}

// Test AMOSWAP.D
void test_amoswap_d() {
    const char *scenario = "AMOSWAP.D: Swap operation on shared_var";
    uint64_t initial = 0xAAAAAAAAAAAAAAAA;
    uint64_t new_val = 0x5555555555555555;
    uint64_t expected_old = initial;
    uint64_t expected_new = new_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic swap
    old_val = do_atomic_swap(&shared_var, new_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOSWAP.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOSWAP.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOADD.D
void test_amoadd_d() {
    const char *scenario = "AMOADD.D: Add operation on shared_var";
    uint64_t initial = 100;
    uint64_t add_val = 50;
    uint64_t expected_old = initial;
    uint64_t expected_new = initial + add_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic add
    old_val = do_atomic_add(&shared_var, add_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOADD.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOADD.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOXOR.D
void test_amoxor_d() {
    const char *scenario = "AMOXOR.D: XOR operation on shared_var";
    uint64_t initial = 0xF0F0F0F0F0F0F0F0;
    uint64_t xor_val = 0x0F0F0F0F0F0F0F0F;
    uint64_t expected_old = initial;
    uint64_t expected_new = initial ^ xor_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic XOR
    old_val = do_atomic_xor(&shared_var, xor_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOXOR.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOXOR.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOOR.D
void test_amoor_d() {
    const char *scenario = "AMOOR.D: OR operation on shared_var";
    uint64_t initial = 0x0F0F0F0F0F0F0F0F;
    uint64_t or_val = 0xF0F0F0F0F0F0F0F0;
    uint64_t expected_old = initial;
    uint64_t expected_new = initial | or_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic OR
    old_val = do_atomic_or(&shared_var, or_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOOR.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOOR.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOAND.D
void test_amoand_d() {
    const char *scenario = "AMOAND.D: AND operation on shared_var";
    uint64_t initial = 0xFFFFFFFF00000000;
    uint64_t and_val = 0x0000FFFF0000FFFF;
    uint64_t expected_old = initial;
    uint64_t expected_new = initial & and_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic AND
    old_val = do_atomic_and(&shared_var, and_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOAND.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOAND.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOMIN.D
void test_amomin_d() {
    const char *scenario = "AMOMIN.D: Minimum operation on shared_var";
    uint64_t initial = 100;
    uint64_t min_val = 50;
    uint64_t expected_old = initial;
    uint64_t expected_new = (initial < min_val) ? initial : min_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic minimum
    old_val = do_atomic_min(&shared_var, min_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOMIN.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOMIN.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOMAX.D
void test_amomax_d() {
    const char *scenario = "AMOMAX.D: Maximum operation on shared_var";
    uint64_t initial = 100;
    uint64_t max_val = 150;
    uint64_t expected_old = initial;
    uint64_t expected_new = (initial > max_val) ? initial : max_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic maximum
    old_val = do_atomic_max(&shared_var, max_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOMAX.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOMAX.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOMINU.D
void test_amominu_d() {
    const char *scenario = "AMOMINU.D: Minimum Unsigned operation on shared_var";
    uint64_t initial = 0xFFFFFFFFFFFFFFFF;
    uint64_t minu_val = 0x0000000000000000;
    uint64_t expected_old = initial;
    uint64_t expected_new = (initial < minu_val) ? initial : minu_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic minimum unsigned
    old_val = do_atomic_minu(&shared_var, minu_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOMINU.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOMINU.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test AMOMAXU.D
void test_amomaxu_d() {
    const char *scenario = "AMOMAXU.D: Maximum Unsigned operation on shared_var";
    uint64_t initial = 0x0000000000000000;
    uint64_t maxu_val = 0xFFFFFFFFFFFFFFFF;
    uint64_t expected_old = initial;
    uint64_t expected_new = (initial > maxu_val) ? initial : maxu_val;
    uint64_t old_val;

    // Initialize shared_var
    shared_var = initial;

    // Perform atomic maximum unsigned
    old_val = do_atomic_maxu(&shared_var, maxu_val);

    // Verify
    bool pass = (expected_old == old_val) && (shared_var == expected_new);

    // Add CHECK_TRUE statements
    CHECK_TRUE(expected_old == old_val, "AMOMAXU.D: Old value does not match expected.");
    CHECK_TRUE(shared_var == expected_new, "AMOMAXU.D: New shared_var value does not match expected.");

    // Add to test results
    add_test_result(scenario, old_val, expected_old, pass);
}

// Test LR.D and SC.D
void test_lr_sc_d() {
    const char *scenario = "LR.D and SC.D: Load Reserved and Store Conditional";
    uint64_t initial = 0x123456789ABCDEF0;
    uint64_t store_val = 0x0FEDCBA987654321;
    uint64_t expected_old = initial;
    uint64_t expected_new = store_val;
    uint64_t loaded_val;
    uint64_t sc_success; // Correctly declared as uint64_t

    // Initialize shared_var
    shared_var = initial;

    // Perform LR.D
    asm volatile (
        "lr.d %0, (%1)"
        : "=&r" (loaded_val)
        : "r" (&shared_var)
        : "memory"
    );

    // Verify LR.D
    bool lr_pass = (expected_old == loaded_val);

    // Perform SC.D
    asm volatile (
        "sc.d %0, %1, (%2)"
        : "=r" (sc_success)
        : "r" (store_val), "r" (&shared_var)
        : "memory"
    );

    // Verify SC.D
    bool sc_pass = (sc_success == 0); // SC.D returns 0 on success

    // Verify shared_var
    bool verify_pass = (shared_var == expected_new);

    // Overall pass condition
    bool pass = lr_pass && sc_pass && verify_pass;

    // Add to test results
    add_test_result(scenario, loaded_val, expected_old, pass);

    CHECK_TRUE(sc_pass, "Store Conditional failed when it should have succeeded.");
    CHECK_TRUE(lr_pass, "LR.D failed: Loaded value does not match expected.");
    CHECK_TRUE(verify_pass, "shared_var was not updated correctly by SC.D.");

}

// Main function to run all tests and print results
int main() {
    // Initialize test counters
    testcase_init();

    // Initialize memory
    memory_init();

    // Run all atomic tests
    test_amoswap_d();
    reset_shared_vars();
    test_amoadd_d();
    reset_shared_vars();
    test_amoxor_d();
    reset_shared_vars();
    test_amoor_d();
    reset_shared_vars();
    test_amoand_d();
    reset_shared_vars();
    test_amomin_d();
    reset_shared_vars();
    test_amomax_d();
    reset_shared_vars();
    test_amominu_d();
    reset_shared_vars();
    test_amomaxu_d();
    reset_shared_vars();
    test_lr_sc_d();

    // Print test header
    printf("%-100s %-25s %-25s %-10s\n", "Scenario", "Loaded/Old Val", "Expected", "Result");
    printf("--------------------------------------------------------------------------------------------------------------\n");

    // Iterate through test_results and print each test
    for (int i = 0; i < current_test; i++) {
        printf("%-100s 0x%016llx 0x%016llx %-10s\n",
               test_results[i].scenario,
               test_results[i].dest_val,
               test_results[i].expected_val,
               test_results[i].pass ? "PASS" : "FAIL");
    }

    // Finalize test and get result
    int result = testcase_finalize();

    // Print overall test result
    if (result == TEST_SUCCESS) {
        printf("\nAll atomic instruction tests passed successfully.\n");
    } else {
        printf("\nSome atomic instruction tests failed.\n");
    }

    return result;
}
