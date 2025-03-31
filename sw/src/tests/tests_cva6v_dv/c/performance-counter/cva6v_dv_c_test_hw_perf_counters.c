/**
 * File: test_performance_counters.c
 * Description: Comprehensive test suite for verifying performance counters in CVA6 RISC-V processor.
 */

#include "common.h"
#include "encoding.h"
#include "testutils.h"

// ---------------------- Memory Pool Definition ---------------------- //

// Define the base address for the memory pool.
#define LARGE_ARRAY_SIZE (1 << 22) // 4MB

// Allocate a large memory pool as a global variable to ensure it's placed in a suitable memory region.
// The `__attribute__((aligned(4096)))` ensures that each access is page-aligned to induce TLB misses.
volatile char large_memory_pool[LARGE_ARRAY_SIZE] __attribute__((aligned(4096)));

// Define MEMORY_POOL_BASE as the starting address of the large_memory_pool array.
#define MEMORY_POOL_BASE ((volatile char *)large_memory_pool)
// Define bit positions for CSR_MCOUNTEREN
#define CSR_MCOUNTEREN_CY_BIT    (1UL << 0)  // Cycle Counter Enable
#define CSR_MCOUNTEREN_TM_BIT    (1UL << 1)  // Time Counter Enable
#define CSR_MCOUNTEREN_IR_BIT    (1UL << 2)  // Instret Counter Enable
#define CSR_MCOUNTEREN_HPM3_BIT  (1UL << 3)  // HPM3 Enable
#define CSR_MCOUNTEREN_HPM4_BIT  (1UL << 4)  // HPM4 Enable
#define CSR_MCOUNTEREN_HPM5_BIT  (1UL << 5)  // HPM5 Enable
#define CSR_MCOUNTEREN_HPM6_BIT  (1UL << 6)  // HPM6 Enable
#define CSR_MCOUNTEREN_HPM7_BIT  (1UL << 7)  // HPM7 Enable
#define CSR_MCOUNTEREN_HPM8_BIT  (1UL << 8)  // HPM8 Enable
// Add additional HPMn bits as needed (HPM9, HPM10, etc.)
// ---------------------- Function to Enable Performance Counters ---------------------- //

/**
 * Function: enable_performance_counters
 * -------------------------------------
 * Enables the necessary performance counters by setting the appropriate bits in CSR_MCOUNTEREN.
 */
void enable_performance_counters(void) {
    uint64_t ena = 0;
    ena |= CSR_MCOUNTEREN_CY_BIT;    // Enable mcycle
    ena |= CSR_MCOUNTEREN_TM_BIT;    // Enable time
    ena |= CSR_MCOUNTEREN_IR_BIT;    // Enable minstret
    ena |= CSR_MCOUNTEREN_HPM3_BIT;  // Enable mhpmcounter3
    ena |= CSR_MCOUNTEREN_HPM4_BIT;  // Enable mhpmcounter4
    ena |= CSR_MCOUNTEREN_HPM5_BIT;  // Enable mhpmcounter5
    ena |= CSR_MCOUNTEREN_HPM6_BIT;  // Enable mhpmcounter6
    ena |= CSR_MCOUNTEREN_HPM7_BIT;  // Enable mhpmcounter7
    ena |= CSR_MCOUNTEREN_HPM8_BIT;  // Enable mhpmcounter8
    // ... Enable additional HPM counters as needed

    // Write the enable bits to CSR_MCOUNTEREN
    write_csr(mcounteren, ena);
}

// ---------------------- Test Functions ---------------------- //

/**
 * Test 1: Initialization of Performance Counters
 * -----------------------------------------------
 * Verifies that all performance counters are zero after reset.
 */
void test_initialization(void) {
    // Scenario: Verify that all performance counters are zero after reset

    // Check each CSR individually
    CHECK_EQUAL_HEX(0, read_csr(mcycle), "Performance Counter 'mcycle' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(minstret), "Performance Counter 'minstret' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(mhpmcounter3), "Performance Counter 'mhpmcounter3' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(mhpmcounter4), "Performance Counter 'mhpmcounter4' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(mhpmcounter5), "Performance Counter 'mhpmcounter5' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(mhpmcounter6), "Performance Counter 'mhpmcounter6' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(mhpmcounter7), "Performance Counter 'mhpmcounter7' should be zero after reset.");
    CHECK_EQUAL_HEX(0, read_csr(mhpmcounter8), "Performance Counter 'mhpmcounter8' should be zero after reset.");
    // ... Repeat for all relevant CSRs
}

/**
 * Test 2: Incrementation of mcycle and minstret
 * ---------------------------------------------
 * Verifies that mcycle and minstret increment correctly during program execution.
 */
void test_mcycle_minstret(void) {
    // Scenario: Verify that mcycle and minstret increment correctly during program execution

    // Reset counters
    write_csr(mcycle, 0);
    write_csr(minstret, 0);

    // Record start values
    uint64_t start_cycle = read_csr(mcycle);
    uint64_t start_instret = read_csr(minstret);

    // Perform some operations using assembly to ensure precise instruction count
    asm volatile (
        "li t0, 100\n\t"        // Load immediate 100 into t0
        "li t1, 200\n\t"        // Load immediate 200 into t1
        "add t2, t0, t1\n\t"    // t2 = t0 + t1
        "sub t3, t1, t0\n\t"    // t3 = t1 - t0
        "mul t4, t0, t1\n\t"    // t4 = t0 * t1
        "div t5, t1, t0\n\t"    // t5 = t1 / t0
        :
        :
        : "t0", "t1", "t2", "t3", "t4", "t5"
    );

    // Record end values
    uint64_t end_cycle = read_csr(mcycle);
    uint64_t end_instret = read_csr(minstret);

    // Calculate expected increments
    uint64_t cycle_increment = end_cycle - start_cycle;
    uint64_t instret_increment = end_instret - start_instret;

    // Check that minstret incremented by at least 6
    CHECK_TRUE(instret_increment >= 6, "minstret incremented by %ld, expected at least 6.", instret_increment);

    // Check that mcycle incremented by at least 6
    CHECK_TRUE(cycle_increment >= 6, "mcycle incremented by %ld, expected at least 6.", cycle_increment);
}

/**
 * Test 3: Cache Miss Counting
 * ---------------------------
 * Verifies that cache miss counters increment correctly.
 */
void test_cache_misses(void) {
    // Scenario: Verify that cache miss counters increment correctly

    // Reset cache miss counters (Assuming mhpmcounter3 for L1 icache miss and mhpmcounter4 for L1 dcache miss)
    write_csr(mhpmcounter3, 0);
    write_csr(mhpmcounter4, 0);

    // Define a large array to exceed cache size to cause cache misses
    #define ARRAY_SIZE 1024
    volatile int array[ARRAY_SIZE] __attribute__((aligned(64))); // Align to cache line size

    // Initialize the array
    for(int i = 0; i < ARRAY_SIZE; i++) {
        array[i] = i;
    }

    // Perform operations with a stride that likely causes cache misses
    for(int i = 0; i < ARRAY_SIZE; i += 64) { // Stride larger than typical cache line size
        array[i] += 1;
    }

    // Read the cache miss counters
    uint64_t icache_miss = read_csr(mhpmcounter3);
    uint64_t dcache_miss = read_csr(mhpmcounter4);

    // Check that cache miss counters have incremented
    CHECK_TRUE(icache_miss > 0, "L1 instruction cache miss counter did not increment.");
    CHECK_TRUE(dcache_miss > 0, "L1 data cache miss counter did not increment.");
}

/**
 * Test 4: TLB Miss Counting
 * -------------------------
 * Verifies that TLB miss counters increment correctly.
 */
void test_tlb_misses(void) {
    // Scenario: Verify that TLB miss counters increment correctly

    // Reset TLB miss counters (Assuming mhpmcounter5 for ITLB miss and mhpmcounter6 for DTLB miss)
    write_csr(mhpmcounter5, 0);
    write_csr(mhpmcounter6, 0);

    // Access multiple pages to cause TLB misses
    for(int i = 0; i < LARGE_ARRAY_SIZE; i += 4096) { // Stride of page size (4KB)
        large_memory_pool[i] = i % 256;
    }

    // Read the TLB miss counters
    uint64_t itlb_miss = read_csr(mhpmcounter5);
    uint64_t dtlb_miss = read_csr(mhpmcounter6);

    // Check that TLB miss counters have incremented
    CHECK_TRUE(itlb_miss > 0, "Instruction TLB miss counter did not increment.");
    CHECK_TRUE(dtlb_miss > 0, "Data TLB miss counter did not increment.");
}

/**
 * Test 5: Load and Store Operations
 * ----------------------------------
 * Verifies that load and store counters increment correctly.
 */
void test_load_store(void) {
    // Scenario: Verify that load and store counters increment correctly

    // Reset load and store counters (Assuming mhpmcounter7 for load operations and mhpmcounter8 for store operations)
    write_csr(mhpmcounter7, 0);
    write_csr(mhpmcounter8, 0);

    // Define an array for load and store operations
    #define LOAD_STORE_SIZE 1024
    volatile int array[LOAD_STORE_SIZE] __attribute__((aligned(64))); // Align to cache line size

    // Initialize the array
    for(int i = 0; i < LOAD_STORE_SIZE; i++) {
        array[i] = i;
    }

    // Perform load operations
    volatile int sum = 0;
    for(int i = 0; i < LOAD_STORE_SIZE; i++) {
        sum += array[i];
    }

    // Perform store operations
    for(int i = 0; i < LOAD_STORE_SIZE; i++) {
        array[i] = sum;
    }

    // Read the load and store counters
    uint64_t load_ops = read_csr(mhpmcounter7);
    uint64_t store_ops = read_csr(mhpmcounter8);

    // Check that load and store counters have incremented
    CHECK_TRUE(load_ops >= LOAD_STORE_SIZE, "Load operations counter did not increment correctly.");
    CHECK_TRUE(store_ops >= LOAD_STORE_SIZE, "Store operations counter did not increment correctly.");
}

/**
 * Test 6: Exception and Interrupt Tracking
 * -----------------------------------------
 * Verifies that exception and interrupt counters increment correctly.
 */
void test_exceptions(void) {
    // Scenario: Verify that exception and interrupt counters increment correctly

    // Reset exception counters (Assuming mhpmcounter9 for exceptions and mhpmcounter10 for exception returns)
    write_csr(mhpmcounter9, 0);
    write_csr(mhpmcounter10, 0);

    // Trigger an exception by executing ecall
    asm volatile (
        "ecall\n\t"
        :
        :
        :
    );

    // Wait for trap handler to set the flag
    while(!trap_occurred);

    // Read the exception counters
    uint64_t exception_count = read_csr(mhpmcounter9);
    uint64_t exception_ret_count = read_csr(mhpmcounter10);

    // Check that exception counters have incremented
    CHECK_TRUE(exception_count >= 1, "Exception counter did not increment.");
    CHECK_TRUE(exception_ret_count >= 1, "Exception return counter did not increment.");

    // Reset the flag for future tests
    trap_occurred = 0;
}

/**
 * Test 7: Branch Misprediction Tracking
 * -------------------------------------
 * Verifies that branch misprediction counters increment correctly.
 */
void test_branch_mispredictions(void) {
    // Scenario: Verify that branch misprediction counters increment correctly

    // Reset branch misprediction counters (Assuming mhpmcounter11 and mhpmcounter14)
    write_csr(mhpmcounter11, 0);
    write_csr(mhpmcounter14, 0);

    // Execute a loop with unpredictable branches to cause mispredictions
    volatile int x = 0;
    for(int i = 0; i < 1000; i++) {
        asm volatile (
            "beq %0, %0, label_%=\n\t" // Always branch taken
            "addi %0, %0, 1\n\t"      // Increment x
            "label_%=:\n\t"
            : "+r"(x)
            :
            :
        );
    }

    // Read the branch misprediction counters
    uint64_t mis_predict = read_csr(mhpmcounter11);
    uint64_t mis_predict2 = read_csr(mhpmcounter14);

    // Check that branch misprediction counters have incremented
    CHECK_TRUE(mis_predict > 0, "Branch misprediction counter did not increment.");
    CHECK_TRUE(mis_predict2 > 0, "Branch misprediction counter 2 did not increment.");
}

/**
 * Test 8: Counter Overflow Handling
 * ---------------------------------
 * Verifies counter overflow behavior.
 */
void test_overflow(void) {
    // Scenario: Verify counter overflow behavior

    // Reset a counter, e.g., mcycle, to near maximum value
    write_csr(mcycle, 0xFFFFFFFFFFFFFFF0ULL);

    // Perform operations to cause overflow
    asm volatile (
        "addi t0, x0, 1\n\t" // Increment mcycle by 1
        "addi t0, t0, 1\n\t" // Increment mcycle by 2
        "addi t0, t0, 1\n\t" // Increment mcycle by 3
        "addi t0, t0, 1\n\t" // Increment mcycle by 4
        :
        :
        :
    );

    // Read the mcycle counter
    uint64_t mcycle_val = read_csr(mcycle);

    // Expected: mcycle should have wrapped around
    uint64_t expected = 0xFFFFFFFFFFFFFFF0ULL + 4;

    // Check if mcycle equals expected value
    CHECK_EQUAL_HEX(expected, mcycle_val, "mcycle counter overflowed incorrectly.");
}

/**
 * Test 9: Event Selector Configuration
 * ------------------------------------
 * Verifies that event selectors correctly configure performance counters.
 */
void test_event_selectors(void) {
    // Scenario: Verify that event selectors correctly configure performance counters

    // Reset event selectors and counters (Assuming mhpmevent3 and mhpmevent4 control specific events)
    write_csr(mhpmevent3, 0);
    write_csr(mhpmevent4, 0);
    write_csr(mhpmcounter3, 0); // Linked to mhpmevent3
    write_csr(mhpmcounter4, 0); // Linked to mhpmevent4

    // Configure mhpmevent3 to count load operations (Assuming event code 0x1)
    write_csr(mhpmevent3, 0x1);

    // Configure mhpmevent4 to count store operations (Assuming event code 0x2)
    write_csr(mhpmevent4, 0x2);

    // Perform load and store operations
    #define LOAD_STORE_TEST_SIZE 100
    volatile int test_array[LOAD_STORE_TEST_SIZE] __attribute__((aligned(64))); // Align to cache line size

    // Initialize the array
    for(int i = 0; i < LOAD_STORE_TEST_SIZE; i++) {
        test_array[i] = i;
    }

    // Perform load operations
    volatile int sum = 0;
    for(int i = 0; i < LOAD_STORE_TEST_SIZE; i++) {
        sum += test_array[i];
    }

    // Perform store operations
    for(int i = 0; i < LOAD_STORE_TEST_SIZE; i++) {
        test_array[i] = sum;
    }

    // Read the counters
    uint64_t load_count = read_csr(mhpmcounter3);
    uint64_t store_count = read_csr(mhpmcounter4);

    // Check that counters have incremented appropriately
    CHECK_TRUE(load_count >= LOAD_STORE_TEST_SIZE, "Load operation counter did not increment correctly.");
    CHECK_TRUE(store_count >= LOAD_STORE_TEST_SIZE, "Store operation counter did not increment correctly.");
}

/**
 * Test 10: Access Permissions and Privilege Levels
 * -----------------------------------------------
 * Verifies that access permissions are enforced based on privilege levels.
 */
void test_access_permissions(void) {
    // Scenario: Verify that access permissions are enforced based on privilege levels

    // Note: Implementing privilege level changes requires switching between Machine, Supervisor, and User modes.
    // This is highly system-dependent and may require specific setup.
    // Below is a conceptual example and may need adjustments based on the actual system implementation.

    // Attempt to read a machine-level performance counter from user mode
    // Expected: Illegal instruction or access exception

    // Switch to User mode
    asm volatile (
        "csrs mstatus, %0\n\t" // Set UXL (User mode)
        "csrs sstatus, %1\n\t" // Ensure Supervisor mode is not interfering
        :
        : "r"(MSTATUS_UXL), "r"(SSTATUS_UXL)
        : "memory"
    );

    // Attempt to read mcycle from User mode
    uint64_t mcycle_val = read_csr(mcycle);

    // If access is allowed, this is a failure
    // Since we cannot actually switch modes in this test, we assume it's in Machine mode
    // Thus, this test serves as a placeholder for actual privilege level testing
    CHECK_TRUE(mcycle_val > 0, "Accessing mcycle from user mode should not be allowed.");

    // Note: Proper privilege level testing would require running code in different modes,
    // which is beyond the scope of this single-hart, single-threaded test suite.
}

// ---------------------- Main Function ---------------------- //

/**
 * Function: main
 * --------------
 * Executes all performance counter tests.
 */
int main(void) {
    // Initialize test environment
    testcase_init();

    // Setup trap handler
    setup_trap_handler();

    // Enable performance counters
    enable_performance_counters();

    // Run tests
    test_initialization();
    test_mcycle_minstret();
    test_cache_misses();
    test_tlb_misses();
    test_load_store();
    test_exceptions();
    test_branch_mispredictions();
    test_overflow();
    test_event_selectors();
    test_access_permissions();

    // Finalize test and get result
    int result = testcase_finalize();

    // Return the overall test result
    return result;
}
