#include "common.h"  // Include the common header file

// Test macros
#define TEST_ASSERT(expr, scenario) \
    if (!(expr)) { \
        printf("Test failed: %s\n", scenario); \
        return 1; \
    } else { \
        printf("Test passed: %s\n", scenario); \
    }

// Function prototypes
int test_mstatus_register();
int test_mtvec_register();
int test_mcause_register();
int test_random_access_csr();
int test_privilege_level_change();
int test_unsupported_csr_access();

// Main test function
int main() {
    printf("Starting CSR tests...\n");

    int result = 0;
    result += test_mstatus_register();
    result += test_mtvec_register();
    result += test_mcause_register();
    result += test_random_access_csr();
    result += test_privilege_level_change();
    result += test_unsupported_csr_access();

    if (result == 0) {
        printf("All CSR tests passed successfully!\n");
    } else {
        printf("Some CSR tests failed.\n");
    }
    return result;
}

// Test mstatus CSR
int test_mstatus_register() {
    printf("\nTesting mstatus register...\n");

    // Save the current mstatus value
    uint64_t original_mstatus;
    asm volatile("csrr %0, mstatus" : "=r"(original_mstatus));

    // Set new values to mstatus and verify
    uint64_t test_value = original_mstatus | 0x8;  // Example test: Set MIE (Machine Interrupt Enable)
    asm volatile("csrw mstatus, %0" :: "r"(test_value));

    uint64_t read_back;
    asm volatile("csrr %0, mstatus" : "=r"(read_back));

    TEST_ASSERT(read_back == test_value, "mstatus: MIE bit set");

    // Restore original mstatus value
    asm volatile("csrw mstatus, %0" :: "r"(original_mstatus));

    return 0;
}

// Test mtvec CSR
int test_mtvec_register() {
    printf("\nTesting mtvec register...\n");

    // Save original mtvec value
    uintptr_t original_mtvec;
    asm volatile("csrr %0, mtvec" : "=r"(original_mtvec));

    // Set mtvec to trap handler and verify
    uintptr_t test_value = (uintptr_t)trap_handler;
    asm volatile("csrw mtvec, %0" :: "r"(test_value));

    uintptr_t read_back;
    asm volatile("csrr %0, mtvec" : "=r"(read_back));

    TEST_ASSERT(read_back == test_value, "mtvec: Set trap handler address");

    // Restore original mtvec value
    asm volatile("csrw mtvec, %0" :: "r"(original_mtvec));

    return 0;
}

// Test mcause CSR
int test_mcause_register() {
    printf("\nTesting mcause register...\n");

    // Save original mtvec value and set the trap handler
    uintptr_t original_mtvec;
    asm volatile("csrr %0, mtvec" : "=r"(original_mtvec));
    asm volatile("csrw mtvec, %0" :: "r"((uintptr_t)trap_handler));

    // Set an instruction breakpoint at a valid, aligned address
    uintptr_t *breakpoint_address = (uintptr_t *)((uintptr_t)test_mcause_register & ~0x3);  // Align to 4-byte boundary
    set_instruction_breakpoint(breakpoint_address);

    // Execute an instruction to trigger the breakpoint
    asm volatile("nop");

    // Read mcause register after triggering a breakpoint
    uint64_t mcause;
    asm volatile("csrr %0, mcause" : "=r"(mcause));

    // Expect cause 3 (Breakpoint exception)
    TEST_ASSERT((mcause & 0xF) == 3, "mcause: Breakpoint exception triggered");

    // Restore original mtvec value
    asm volatile("csrw mtvec, %0" :: "r"(original_mtvec));

    return 0;
}


int test_random_access_csr() {
    printf("\nTesting random access to a set of valid CSRs...\n");

    // List of writable CSR addresses
    uint32_t csr_addresses[] = {0x300}; // Test with mstatus
    size_t num_csrs = sizeof(csr_addresses) / sizeof(csr_addresses[0]);
    uint64_t original_value, test_value = 0x12345678;

    for (size_t i = 0; i < num_csrs; i++) {
        uint32_t csr_index = csr_addresses[i];

        // Read original CSR value
        asm volatile("csrr %0, %1" : "=r"(original_value) : "i"(csr_index));

        // Write test value to CSR
        asm volatile("csrrw %0, %1, %2" : "=r"(original_value) : "i"(csr_index), "r"(test_value));

        // Read back and verify
        uint64_t read_back;
        asm volatile("csrr %0, %1" : "=r"(read_back) : "i"(csr_index));

        // Ensure read-back value matches test value
        TEST_ASSERT(read_back == test_value, "Random CSR access: Valid CSR read-write test");

        // Restore original value
        asm volatile("csrw %0, %1" :: "i"(csr_index), "r"(original_value));
    }

    return 0;
}


int test_privilege_level_change() {
    printf("\nTesting privilege level changes...\n");

    // Save original mstatus value
    uint64_t original_mstatus;
    asm volatile("csrr %0, mstatus" : "=r"(original_mstatus));

    // Set MPP (Machine Previous Privilege) bits to User mode (0x0)
    uint64_t user_mode_status = (original_mstatus & ~(3 << 11)); // Clear MPP bits for User mode
    asm volatile("csrw mstatus, %0" :: "r"(user_mode_status));

    // Set mepc to a properly aligned return address
    uintptr_t return_address = (uintptr_t)test_privilege_level_change & ~0x3;  // Align to 4-byte boundary
    asm volatile("csrw mepc, %0" :: "r"(return_address));

    // Simulate return to User mode using mret
    asm volatile("mret");

    // Verify the change in mstatus after mret
    uint64_t mstatus;
    asm volatile("csrr %0, mstatus" : "=r"(mstatus));

    TEST_ASSERT((mstatus & (3 << 11)) == 0, "Privilege level: Change to User mode");

    // Restore original mstatus
    asm volatile("csrw mstatus, %0" :: "r"(original_mstatus));

    return 0;
}




// Test unsupported CSR access
int test_unsupported_csr_access() {
    printf("\nTesting unsupported CSR access...\n");

    // Try to access an unsupported CSR and handle the trap
    uint64_t result = 0;
    asm volatile("csrr %0, 0xBAD" : "=r"(result));  // Attempt to read a non-existent CSR

    // Ensure the system handled the exception
    TEST_ASSERT(trap_occurred, "Unsupported CSR: Access results in trap");

    return 0;
}
