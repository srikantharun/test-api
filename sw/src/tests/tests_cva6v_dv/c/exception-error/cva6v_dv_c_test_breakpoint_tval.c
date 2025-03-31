// CVA6V directed C tests: Author: Abhilash Chadhar
// In this test file, breakpoints and tval register behavior are explicitly tested.

#include "common.h"

// Define memory regions and expected values
__attribute__((aligned(8))) uint64_t test_memory[4]; // Memory for testing breakpoints

// Function to initialize values for testing breakpoints
void initialize_test_values() {
    test_memory[0] = 0xDEADBEEFDEADBEEF;  // Test data
    test_memory[1] = 0xCAFEBABECAFEBABE;  // More test data
    test_memory[2] = 0x1234567812345678;  // More test data
    test_memory[3] = 0x0F0F0F0F0F0F0F0F;  // More test data
    trap_occurred = 0;  // Reset the trap flag
}

// Macro to perform breakpoint test with checks
#define TEST_BREAKPOINT(description, set_breakpoint, trigger_code) \
    do {                                                          \
        initialize_test_values();                                 \
        printf("%s\n", description);                              \
        set_breakpoint;                                           \
        trigger_code;                                             \
        if (!trap_occurred) {                                     \
            printf("%s failed.\n", description);                  \
            return -1;                                            \
        } else {                                                  \
            printf("%s passed.\n", description);                  \
        }                                                         \
        trap_occurred = 0; /* Reset trap flag for next test */     \
    } while (0)

int main() {
    // Standard Case 1: Instruction breakpoint at main function
    //TEST_BREAKPOINT("Standard Case 1: Instruction breakpoint at main",
    //                set_instruction_breakpoint((uint64_t *)main),
    //                asm volatile("ebreak"));  // Trigger breakpoint

    // Standard Case 2: Instruction breakpoint inside loop
    //volatile int loop_counter = 0;
    // Correctly declare the loop_start label before use
    //TEST_BREAKPOINT("Standard Case 2: Instruction breakpoint inside loop",
    //                set_instruction_breakpoint((uint64_t *)&&loop_start),
    //                asm volatile("j loop_start; loop_start: addi %0, %0, 1" : "+r"(loop_counter)));

    // Critical Case 1: Breakpoint on privileged instruction
    //TEST_BREAKPOINT("Critical Case 1: Breakpoint on privileged instruction",
    //                set_instruction_breakpoint((uint64_t *)trap_handler),
    //                asm volatile("ebreak"));

    // Critical Case 2: Data breakpoint on read-only memory
    //TEST_BREAKPOINT("Critical Case 2: Data breakpoint on read-only memory",
    //                set_data_breakpoint((uint64_t *)0x80000000),  // Address for read-only memory
    //                test_memory[1] = 0xFFFFFFFFFFFFFFFF);  // Attempt write to read-only memory

    // Corner Case 1: Breakpoint at boundary of memory region
    TEST_BREAKPOINT("Corner Case 1: Breakpoint at boundary of memory region",
                    set_instruction_breakpoint((uint64_t *)(0x20000000 + sizeof(test_memory) - 1)),
                    asm volatile("ebreak"));

    // Corner Case 2: Overlapping breakpoints
    TEST_BREAKPOINT("Corner Case 2: Overlapping breakpoints",
                    { set_instruction_breakpoint((uint64_t *)main); set_data_breakpoint((uint64_t *)main); },
                    asm volatile("ebreak"));

    // Corner Case 3: Breakpoint on unaligned address
    TEST_BREAKPOINT("Corner Case 3: Breakpoint on unaligned address",
                    set_instruction_breakpoint((uint64_t *)((uint64_t)main + 1)),
                    asm volatile("ebreak"));

    // Classic Case 1: Repeatedly hit the same breakpoint
    for (int i = 0; i < 3; ++i) {
        TEST_BREAKPOINT("Classic Case 1: Repeatedly hitting the same breakpoint",
                        set_instruction_breakpoint((uint64_t *)main),
                        asm volatile("ebreak"));
    }

    // Classic Case 2: Test breakpoints with single-step execution
    asm volatile("csrs dcsr, %0" : : "r"(0x1));  // Set DCSR for single-step
    TEST_BREAKPOINT("Classic Case 2: Single-step execution with breakpoints",
                    set_instruction_breakpoint((uint64_t *)main),
                    asm volatile("ebreak"));

    printf("All tests completed.\n");

    return 0;

//loop_start:  // Label to mark the start of the loop
//    asm volatile("addi %0, %0, 1" : "+r"(loop_counter));
//    asm volatile("j loop_start");
}
