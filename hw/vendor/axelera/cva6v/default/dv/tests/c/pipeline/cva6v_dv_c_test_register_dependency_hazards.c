#include "common.h"

#define NUM_ADV_TESTS 20  // Increased number of tests for advanced register dependency hazards

// Expected results for advanced register dependency hazard tests
uint32_t expected_adv_results[NUM_ADV_TESTS] = {
    0x5, 0xF, 0x2, 0x5, 0x6, 0xF, 0x1, 0x4, 0xA, 0xA, 0xC, 0x2,
    0x8, 0x5, 0x3, 0xA, 0xC, 0xF, 0x6, 0x8
};

// Memory to store the results
uint32_t adv_results[NUM_ADV_TESTS];

// Define addresses to use within the cacheable memory region
volatile uint32_t *adv_mem_address_0 = (volatile uint32_t *)0x2000000040;  // Aligned to 64 bytes
volatile uint32_t *adv_mem_address_1 = (volatile uint32_t *)0x2000000080;  // Aligned to 64 bytes

// Inline assembly function to test advanced register dependency hazards
void test_advanced_register_dependency_hazards() {
    // RAW Hazard: Test with Addition and Subtraction
    __asm__ volatile (
        "li t0, 0x2;"             // Load immediate value 0x2 into t0
        "li t1, 0x3;"             // Load immediate value 0x3 into t1
        "add t2, t0, t1;"         // Add t0 and t1, result in t2 (5)
        "sub t3, t2, t1;"         // Subtract t1 from t2 (should be 2)
        "add t4, t3, t1;"         // Add t1 to t3, expecting t4 = 5
        "sw t4, %0;"              // Store result to adv_results[0]
        : "=m"(adv_results[0])
    );

    // RAW Hazard: Test with Multiplication and Addition
    __asm__ volatile (
        "li t0, 0x2;"             // Load immediate value 0x2 into t0
        "li t1, 0x5;"             // Load immediate value 0x5 into t1
        "mul t2, t0, t1;"         // Multiply t0 by t1, result in t2 (10)
        "addi t3, t2, 5;"         // Add immediate value 5 to t2 (15)
        "sw t3, %0;"              // Store result to adv_results[1]
        : "=m"(adv_results[1])
    );

    // WAW Hazard: Test with Division and Multiplication
    __asm__ volatile (
        "li t0, 0x8;"             // Load immediate value 0x8 into t0
        "li t1, 0x4;"             // Load immediate value 0x4 into t1
        "div t2, t0, t1;"         // Divide t0 by t1, result in t2 (2)
        "mul t2, t2, t1;"         // Multiply t2 by t1, result in t2 (8)
        "div t2, t2, t1;"         // Divide t2 by t1, result should remain 2
        "sw t2, %0;"              // Store result to adv_results[2]
        : "=m"(adv_results[2])
    );

    // WAR Hazard: Test with Multiple Read-After-Write Dependencies
    __asm__ volatile (
        "li t0, 0x3;"             // Load immediate value 0x3 into t0
        "li t1, 0x2;"             // Load immediate value 0x2 into t1
        "addi t2, t0, 0x1;"       // Add immediate 1 to t0, result in t2 (4)
        "sub t3, t2, t1;"         // Subtract t1 from t2 (2)
        "mul t4, t3, t1;"         // Multiply t3 by t1 (4)
        "addi t5, t4, 0x1;"       // Add immediate 1 to t4, result in t5 (5)
        "sw t5, %0;"              // Store result to adv_results[3]
        : "=m"(adv_results[3])
    );

    // Complex WAR Hazard: Interleaved Read-After-Write with Delayed Loads
    __asm__ volatile (
        "li t0, 0x6;"             // Load immediate value 0x6 into t0
        "li t1, 0x7;"             // Load immediate value 0x7 into t1
        "add t2, t0, t1;"         // Add t0 and t1 (13)
        "sub t3, t2, t1;"         // Subtract t1 from t2 (6)
        "add t4, t3, t0;"         // Add t0 to t3 (12)
        "sub t5, t4, t0;"         // Subtract t0 from t4 (6)
        "sw t5, %0;"              // Store result to adv_results[4]
        : "=m"(adv_results[4])
    );

    // Load-Use Hazard: Test with Delayed Load and Use
    __asm__ volatile (
        "li t0, 0xF;"             // Load immediate value 0xF into t0
        "sw t0, 0(%[addr0]);"     // Store t0 to memory address pointed by addr0
        "lw t1, 0(%[addr0]);"     // Load value from memory into t1
        "addi t2, t1, 0x0;"       // Add immediate 0 to t1 (no change)
        "sw t2, %0;"              // Store result to adv_results[5]
        : "=m"(adv_results[5])
        : [addr0] "r"(adv_mem_address_0)
    );

    // Load-Use Hazard: Involving a Conditional Branch
    __asm__ volatile (
        "li t0, 0x1;"             // Load immediate value 0x1 into t0
        "sw t0, 0(%[addr1]);"     // Store t0 to memory address pointed by addr1
        "lw t1, 0(%[addr1]);"     // Load value from memory into t1
        "bnez t1, 1f;"            // Branch if t1 is not zero
        "addi t2, zero, 0x0;"     // Set t2 to zero if branch not taken
        "j 2f;"                   // Jump to the end
        "1: addi t2, zero, 0x1;"  // Set t2 to 1 if branch taken
        "2: sw t2, %0;"           // Store result to adv_results[6]
        : "=m"(adv_results[6])
        : [addr1] "r"(adv_mem_address_1)
    );

    // Complex Register Dependency: Using Multiple Forwarding Paths
    __asm__ volatile (
        "li t0, 0x2;"             // Load immediate value 0x2 into t0
        "li t1, 0x2;"             // Load immediate value 0x2 into t1
        "mul t2, t0, t1;"         // Multiply t0 by t1, result in t2 (4)
        "add t3, t2, t1;"         // Add t1 to t2, result in t3 (6)
        "sub t4, t3, t1;"         // Subtract t1 from t3, result in t4 (4)
        "sw t4, %0;"              // Store result to adv_results[7]
        : "=m"(adv_results[7])
    );

    // WAW Hazard: Verify Correct Register Reordering in Complex Calculations
    __asm__ volatile (
        "li t0, 0x8;"             // Load immediate value 0x8 into t0
        "li t1, 0x2;"             // Load immediate value 0x2 into t1
        "div t2, t0, t1;"         // Divide t0 by t1 (4)
        "mul t2, t2, t1;"         // Multiply t2 by t1, result in t2 (8)
        "addi t2, t2, 0x2;"       // Add immediate 2 to t2, result in t2 (10)
        "sw t2, %0;"              // Store result to adv_results[8]
        : "=m"(adv_results[8])
    );

    // Advanced WAR Hazard: Using Complex Subtractions and Additions
    __asm__ volatile (
        "li t0, 0xA;"             // Load immediate value 0xA into t0
        "li t1, 0x3;"             // Load immediate value 0x3 into t1
        "sub t2, t0, t1;"         // Subtract t1 from t0, result in t2 (7)
        "add t2, t2, t1;"         // Add t1 to t2, result in t2 (10)
        "sw t2, %0;"              // Store result to adv_results[9]
        : "=m"(adv_results[9])
    );

    // Load-Store Hazard: Validate Correct Handling of Load-Followed-by-Store Sequence
    __asm__ volatile (
        "li t0, 0x4;"             // Load immediate value 0x4 into t0
        "li t1, 0x8;"             // Load immediate value 0x8 into t1
        "sw t0, 0(%[addr0]);"     // Store t0 at memory address pointed by addr0
        "lw t2, 0(%[addr0]);"     // Load value back from memory into t2
        "add t3, t2, t1;"         // Add t1 to t2, expecting t3 = 12
        "sw t3, %0;"              // Store result to adv_results[10]
        : "=m"(adv_results[10])
        : [addr0] "r"(adv_mem_address_0)
    );

    // Load-Store-Load Hazard: Complex Sequential Load and Store with Branching
    __asm__ volatile (
        "li t0, 0x1;"             // Load immediate value 0x1 into t0
        "sw t0, 0(%[addr1]);"     // Store t0 at memory address pointed by addr1
        "lw t1, 0(%[addr1]);"     // Load value back from memory into t1
        "addi t2, t1, 0x1;"       // Increment t1 by 1, result in t2
        "sw t2, 0(%[addr1]);"     // Store t2 back to memory
        "lw t3, 0(%[addr1]);"     // Load the new value back from memory
        "sw t3, %0;"              // Store result to adv_results[11]
        : "=m"(adv_results[11])
        : [addr1] "r"(adv_mem_address_1)
    );

    // RAW Hazard: Sequential Load-Store Dependencies
    __asm__ volatile (
        "li t0, 0x4;"             // Load immediate value 0x4 into t0
        "sw t0, 0(%[addr0]);"     // Store t0 at memory address pointed by addr0
        "lw t1, 0(%[addr0]);"     // Load value from memory into t1
        "add t2, t1, t0;"         // Add t1 to t0, result in t2 (8)
        "sw t2, %0;"              // Store result to adv_results[12]
        : "=m"(adv_results[12])
        : [addr0] "r"(adv_mem_address_0)
    );

    // WAR Hazard: Complex Operations with Delays
    __asm__ volatile (
        "li t0, 0x3;"             // Load immediate value 0x3 into t0
        "li t1, 0x2;"             // Load immediate value 0x2 into t1
        "and t2, t0, t1;"         // AND t0 and t1, result in t2 (2)
        "ori t3, t2, 0x7;"        // OR immediate 0x7 to t2, result in t3 (7)
        "xor t4, t3, t1;"         // XOR t3 and t1, result in t4 (5)
        "sw t4, %0;"              // Store result to adv_results[13]
        : "=m"(adv_results[13])
    );

    // WAW Hazard: Write Dependency after Branch
    __asm__ volatile (
        "li t0, 0x1;"             // Load immediate value 0x1 into t0
        "li t1, 0x3;"             // Load immediate value 0x3 into t1
        "bne t0, t1, 1f;"         // Branch if t0 is not equal to t1
        "li t2, 0x9;"             // This instruction should not execute
        "j 2f;"                   // Jump to the end
        "1: li t2, 0x3;"          // Set t2 to 0x3 if branch is taken
        "2: addi t2, t2, 0x0;"    // Ensure no side effects after jump
        "sw t2, %0;"              // Store result to adv_results[14]
        : "=m"(adv_results[14])
    );

    // Complex Load-Use Hazards with Data Dependency Loop
    __asm__ volatile (
        "li t0, 0x1;"             // Initialize loop counter t0
        "li t1, 0x5;"             // Loop limit
        "li t2, 0x0;"             // Accumulator
        "3: add t2, t2, t0;"      // Add loop counter to accumulator
        "addi t0, t0, 1;"         // Increment loop counter
        "blt t0, t1, 3b;"         // Loop back if t0 < t1
        "sw t2, %0;"              // Store result to adv_results[15]
        : "=m"(adv_results[15])
    );

    // Pipeline Bubble Test: Introducing NOPs to Check Hazard Resolution
    __asm__ volatile (
        "li t0, 0x4;"             // Load immediate value 0x4 into t0
        "nop;"                    // No operation
        "nop;"                    // No operation
        "li t1, 0x8;"             // Load immediate value 0x8 into t1
        "nop;"                    // No operation
        "add t2, t0, t1;"         // Add t0 and t1, result in t2 (12)
        "sw t2, %0;"              // Store result to adv_results[16]
        : "=m"(adv_results[16])
    );

    // RAW Hazard with Interleaved Arithmetic and Logical Operations
    __asm__ volatile (
        "li t0, 0xF;"             // Load immediate value 0xF into t0
        "li t1, 0x1;"             // Load immediate value 0x1 into t1
        "sll t2, t0, t1;"         // Shift left t0 by 1 (0x1E)
        "addi t3, t2, 0x1;"       // Add immediate 1 to t2 (0x1F)
        "sra t4, t3, t1;"         // Shift right arithmetic t3 by 1 (0xF)
        "sw t4, %0;"              // Store result to adv_results[17]
        : "=m"(adv_results[17])
    );

    // WAR Hazard with Dependencies Across Arithmetic and Logical Operations
    __asm__ volatile (
        "li t0, 0x4;"             // Load immediate value 0x4 into t0
        "li t1, 0x2;"             // Load immediate value 0x2 into t1
        "div t2, t0, t1;"         // Divide t0 by t1 (2)
        "mul t3, t2, t1;"         // Multiply t2 by t1, result in t3 (4)
        "add t4, t3, t1;"         // Add t1 to t3, result in t4 (6)
        "sw t4, %0;"              // Store result to adv_results[18]
        : "=m"(adv_results[18])
    );

    // WAW Hazard with Sequential Additions and Subtractions
    __asm__ volatile (
        "li t0, 0x8;"             // Load immediate value 0x8 into t0
        "li t1, 0x2;"             // Load immediate value 0x2 into t1
        "add t2, t0, t1;"         // Add t0 and t1, result in t2 (10)
        "sub t2, t2, t1;"         // Subtract t1 from t2, result in t2 (8)
        "sw t2, %0;"              // Store result to adv_results[19]
        : "=m"(adv_results[19])
    );
}

int main() {
    testcase_init();  // Initialize test case

    test_advanced_register_dependency_hazards();
    printf("\nRegister Hazards Test start - \n");

    // Check results using testutils functions and provide specific details for each test
    for (int i = 0; i < NUM_ADV_TESTS; i++) {
        // Print detailed descriptions for each test scenario
        switch (i) {
            case 0:
                printf("\nTest 0: RAW Hazard with Addition and Subtraction\n");
                printf("Description: Verifies proper forwarding for dependent instructions (addition and subtraction) executed back-to-back.\n");
                break;
            case 1:
                printf("\nTest 1: RAW Hazard with Multiplication and Addition\n");
                printf("Description: Checks if pipeline handles RAW hazard by forwarding results of multiplication to an immediate addition.\n");
                break;
            case 2:
                printf("\nTest 2: WAW Hazard with Division and Multiplication\n");
                printf("Description: Ensures that WAW hazard management correctly orders writebacks for division and multiplication on the same register.\n");
                break;
            case 3:
                printf("\nTest 3: WAR Hazard with Multiple Dependencies\n");
                printf("Description: Confirms proper handling of interleaved read-after-write dependencies across multiple operations.\n");
                break;
            case 4:
                printf("\nTest 4: Complex WAR Hazard with Delayed Loads\n");
                printf("Description: Tests interleaved WAR hazards with mixed instructions to simulate pipeline delays and verify forwarding paths.\n");
                break;
            case 5:
                printf("\nTest 5: Load-Use Hazard with Delayed Load\n");
                printf("Description: Validates correct handling of a load-use hazard scenario where a load's result is used after a delay.\n");
                break;
            case 6:
                printf("\nTest 6: Load-Use Hazard Involving a Conditional Branch\n");
                printf("Description: Ensures the pipeline correctly handles a load-use hazard when a conditional branch depends on the load.\n");
                break;
            case 7:
                printf("\nTest 7: Complex Register Dependency Using Forwarding Paths\n");
                printf("Description: Verifies multiple forwarding paths are managed correctly in complex register dependencies.\n");
                break;
            case 8:
                printf("\nTest 8: WAW Hazard with Multiple Writebacks\n");
                printf("Description: Tests the processor's ability to correctly order writes in the presence of write-after-write hazards.\n");
                break;
            case 9:
                printf("\nTest 9: Advanced WAR Hazard with Subtractions and Additions\n");
                printf("Description: Validates proper execution ordering in the presence of read-after-write dependencies with mixed operations.\n");
                break;
            case 10:
                printf("\nTest 10: Load-Store Hazard Validation\n");
                printf("Description: Confirms correct execution of a load followed by a store and subsequent arithmetic operations.\n");
                break;
            case 11:
                printf("\nTest 11: Complex Load-Store-Load Hazard\n");
                printf("Description: Tests handling of load-store-load sequences with intermediate calculations and branching.\n");
                break;
            case 12:
                printf("\nTest 12: RAW Hazard with Sequential Load-Store Dependencies\n");
                printf("Description: Verifies pipeline handling of back-to-back load and store dependencies.\n");
                break;
            case 13:
                printf("\nTest 13: WAR Hazard with Complex Operations and Delays\n");
                printf("Description: Tests pipeline's handling of mixed arithmetic and logical operations with read-after-write hazards.\n");
                break;
            case 14:
                printf("\nTest 14: WAW Hazard Involving Branch and Write Dependency\n");
                printf("Description: Ensures the pipeline correctly handles write-after-write hazards following a conditional branch.\n");
                break;
            case 15:
                printf("\nTest 15: Complex Load-Use Hazard with Data Dependency Loop\n");
                printf("Description: Tests if the pipeline resolves hazards in a loop with a load-use data dependency.\n");
                break;
            case 16:
                printf("\nTest 16: Pipeline Bubble Test with NOPs\n");
                printf("Description: Verifies if the pipeline correctly handles NOPs and resolves hazards across multiple stages.\n");
                break;
            case 17:
                printf("\nTest 17: RAW Hazard with Interleaved Arithmetic and Logical Operations\n");
                printf("Description: Confirms that pipeline handles RAW hazards involving interleaved arithmetic and logical operations.\n");
                break;
            case 18:
                printf("\nTest 18: WAR Hazard Across Arithmetic and Logical Operations\n");
                printf("Description: Verifies correct handling of WAR hazards across different types of operations.\n");
                break;
            case 19:
                printf("\nTest 19: WAW Hazard with Sequential Additions and Subtractions\n");
                printf("Description: Ensures the processor handles sequential write-after-write hazards properly.\n");
                break;
        }

        // Print the expected and actual results
        printf("Expected: 0x%x, Got: 0x%x\n", expected_adv_results[i], adv_results[i]);
        CHECK_EQUAL_INT(expected_adv_results[i], adv_results[i], "Test %d: Expected 0x%x, Got 0x%x", i, expected_adv_results[i], adv_results[i]);
    }

    return testcase_finalize();  // Finalize test case and return result
}
