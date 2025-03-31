// structural_hazard_test.c
// Author: Abhilash Chadhar

#include "common.h"
#include <math.h>

// Define global variables for memory operations
volatile uint32_t memory_a = 0;
volatile uint32_t memory_b = 0;
volatile uint32_t memory_c = 0;
volatile uint32_t memory_d = 0;

// Scenario 1: ALU Resource Contention
void test_alu_contention() {
    PRINT_HEADER();
    printf("Testing ALU Resource Contention...\n");

    // Initialize variables
    uint32_t a = 1;
    uint32_t b = 2;
    uint32_t c = 3;
    uint32_t d = 4;
    uint32_t result1, result2, result3, result4;

    // Perform multiple ALU operations using inline assembly
    asm volatile (
        "add %[res1], %[a], %[b] \n\t"
        "sub %[res2], %[c], %[d] \n\t"
        "xor %[res3], %[a], %[c] \n\t"
        "or  %[res4], %[b], %[d] \n\t"
        : [res1] "=r" (result1),
          [res2] "=r" (result2),
          [res3] "=r" (result3),
          [res4] "=r" (result4)
        : [a] "r" (a),
          [b] "r" (b),
          [c] "r" (c),
          [d] "r" (d)
    );

    // Expected results
    uint32_t expected1 = a + b;
    uint32_t expected2 = c - d;
    uint32_t expected3 = a ^ c;
    uint32_t expected4 = b | d;

    // Verify results
    CHECK_EQUAL_INT(expected1, result1, "ALU Add operation failed.");
    CHECK_EQUAL_INT(expected2, result2, "ALU Sub operation failed.");
    CHECK_EQUAL_INT(expected3, result3, "ALU XOR operation failed.");
    CHECK_EQUAL_INT(expected4, result4, "ALU OR operation failed.");

    // Print results
    PRINT_RESULT("ALU Resource Contention: ADD, SUB, XOR, OR",
                "Computed", "Expected", "Result");

    char res1_str[25], res2_str[25], res3_str[25], res4_str[25];
    int_to_str(result1, res1_str);
    int_to_str(result2, res2_str);
    int_to_str(result3, res3_str);
    int_to_str(result4, res4_str);

    char expected1_str[25], expected2_str[25], expected3_str[25], expected4_str[25];
    int_to_str(expected1, expected1_str);
    int_to_str(expected2, expected2_str);
    int_to_str(expected3, expected3_str);
    int_to_str(expected4, expected4_str);

    // Detailed individual results
    PRINT_RESULT("ADD", res1_str, expected1_str, (result1 == expected1) ? "PASS" : "FAIL");
    PRINT_RESULT("SUB", res2_str, expected2_str, (result2 == expected2) ? "PASS" : "FAIL");
    PRINT_RESULT("XOR", res3_str, expected3_str, (result3 == expected3) ? "PASS" : "FAIL");
    PRINT_RESULT("OR",  res4_str, expected4_str, (result4 == expected4) ? "PASS" : "FAIL");
}

// Scenario 2: Load/Store Unit Contention
void test_load_store_contention() {
    PRINT_HEADER();
    printf("Testing Load/Store Unit Contention...\n");

    // Initialize memory locations
    memory_a = 10;
    memory_b = 20;
    memory_c = 30;
    memory_d = 40;

    uint32_t loaded_a, loaded_b;
   // Expected results
    uint32_t expected_a = memory_a; // 10
    uint32_t expected_b = memory_b; // 20
    uint32_t expected_c = memory_c + 10; // 30 + 10 = 40
    uint32_t expected_d = memory_d + 10; // 40 + 10 = 50
    // Perform multiple load and store operations using inline assembly
    asm volatile (
        "lw %[la], 0(%[pa]) \n\t" // Load from memory_a
        "lw %[lb], 0(%[pb]) \n\t" // Load from memory_b
        "sw %[lc], 0(%[pc]) \n\t" // Store to memory_c (memory_c + 10)
        "sw %[ld], 0(%[pd]) \n\t" // Store to memory_d (memory_d + 10)
        : [la] "=r" (loaded_a),
          [lb] "=r" (loaded_b)
        : [pa] "r" (&memory_a),
          [pb] "r" (&memory_b),
          [lc] "r" (memory_c + 10),
          [ld] "r" (memory_d + 10),
          [pc] "r" (&memory_c),
          [pd] "r" (&memory_d)
    );



    // Verify loaded values
    CHECK_EQUAL_INT(expected_a, loaded_a, "Load from memory_a failed.");
    CHECK_EQUAL_INT(expected_b, loaded_b, "Load from memory_b failed.");

    // Verify stored values
    CHECK_EQUAL_INT(expected_c, memory_c, "Store to memory_c failed.");
    CHECK_EQUAL_INT(expected_d, memory_d, "Store to memory_d failed.");

    // Print results
    PRINT_RESULT("Load/Store Unit Contention",
                "Computed", "Expected", "Result");

    char loaded_a_str[25], loaded_b_str[25];
    int_to_str(loaded_a, loaded_a_str);
    int_to_str(loaded_b, loaded_b_str);
    char expected_a_str[25], expected_b_str[25];
    int_to_str(expected_a, expected_a_str);
    int_to_str(expected_b, expected_b_str);

    PRINT_RESULT("Load memory_a", loaded_a_str, expected_a_str, (loaded_a == expected_a) ? "PASS" : "FAIL");
    PRINT_RESULT("Load memory_b", loaded_b_str, expected_b_str, (loaded_b == expected_b) ? "PASS" : "FAIL");

    char memory_c_str[25], memory_d_str[25];
    int_to_str(memory_c, memory_c_str);
    int_to_str(memory_d, memory_d_str);
    char expected_c_str[25], expected_d_str[25];
    int_to_str(expected_c, expected_c_str);
    int_to_str(expected_d, expected_d_str);

    PRINT_RESULT("Store memory_c", memory_c_str, expected_c_str, (memory_c == expected_c) ? "PASS" : "FAIL");
    PRINT_RESULT("Store memory_d", memory_d_str, expected_d_str, (memory_d == expected_d) ? "PASS" : "FAIL");
}

// Scenario 3: FPU Resource Contention
void test_fpu_contention() {
    PRINT_HEADER();
    printf("Testing FPU Resource Contention...\n");

    // Initialize floating-point variables
    float fa = 1.5f;
    float fb = 2.5f;
    float fc = 3.5f;
    float fd = 4.5f;

    float result1, result2, result3, result4;

    // Perform multiple FPU operations using inline assembly
    asm volatile (
        "fadd.s %[res1], %[a], %[b] \n\t"
        "fsub.s %[res2], %[c], %[d] \n\t"
        "fmul.s %[res3], %[a], %[c] \n\t"
        "fdiv.s %[res4], %[b], %[d] \n\t"
        : [res1] "=f" (result1),
          [res2] "=f" (result2),
          [res3] "=f" (result3),
          [res4] "=f" (result4)
        : [a] "f" (fa),
          [b] "f" (fb),
          [c] "f" (fc),
          [d] "f" (fd)
    );

    // Expected results
    float expected1 = fa + fb; // 4.0f
    float expected2 = fc - fd; // -1.0f
    float expected3 = fa * fc; // 5.25f
    float expected4 = fb / fd; // ≈0.555556f

    // Verify results using local float comparison with tolerance
    CHECK_TRUE(fabsf(result1 - expected1) < FLOAT_TOLERANCE, "FPU Add operation failed.");
    CHECK_TRUE(fabsf(result2 - expected2) < FLOAT_TOLERANCE, "FPU Sub operation failed.");
    CHECK_TRUE(fabsf(result3 - expected3) < FLOAT_TOLERANCE, "FPU Mul operation failed.");
    CHECK_TRUE(fabsf(result4 - expected4) < FLOAT_TOLERANCE, "FPU Div operation failed.");

    // Print results
    PRINT_RESULT("FPU Resource Contention",
                "Computed", "Expected", "Result");

    char result1_str[25], result2_str[25], result3_str[25], result4_str[25];
    float_to_str(result1, result1_str, 6);
    float_to_str(result2, result2_str, 6);
    float_to_str(result3, result3_str, 6);
    float_to_str(result4, result4_str, 6);

    char expected1_str[25], expected2_str[25], expected3_str[25], expected4_str[25];
    float_to_str(expected1, expected1_str, 6);
    float_to_str(expected2, expected2_str, 6);
    float_to_str(expected3, expected3_str, 6);
    float_to_str(expected4, expected4_str, 6);

    // Detailed individual results
    PRINT_RESULT("FPU Add", result1_str, expected1_str, (fabsf(result1 - expected1) < FLOAT_TOLERANCE) ? "PASS" : "FAIL");
    PRINT_RESULT("FPU Sub", result2_str, expected2_str, (fabsf(result2 - expected2) < FLOAT_TOLERANCE) ? "PASS" : "FAIL");
    PRINT_RESULT("FPU Mul", result3_str, expected3_str, (fabsf(result3 - expected3) < FLOAT_TOLERANCE) ? "PASS" : "FAIL");
    PRINT_RESULT("FPU Div", result4_str, expected4_str, (fabsf(result4 - expected4) < FLOAT_TOLERANCE) ? "PASS" : "FAIL");
}

// Scenario 4: Mixed ALU and FPU Operations
void test_mixed_alu_fpu() {
    PRINT_HEADER();
    printf("Testing Mixed ALU and FPU Operations...\n");

    // Initialize variables
    uint32_t a = 5, b = 3;
    float fa = 2.0f, fb = 4.0f;

    uint32_t alu_result;
    float fpu_result;

    // Perform mixed ALU and FPU operations using inline assembly
    asm volatile (
        "add %[alu_res], %[a], %[b] \n\t"      // ALU add
        "fadd.s %[fpu_res], %[fa], %[fb] \n\t" // FPU add
        : [alu_res] "=r" (alu_result),
          [fpu_res] "=f" (fpu_result)
        : [a] "r" (a),
          [b] "r" (b),
          [fa] "f" (fa),
          [fb] "f" (fb)
    );

    // Expected results
    uint32_t expected_alu = a + b; // 8
    float expected_fpu = fa + fb; // 6.0f

    // Verify results using local float comparison for FPU
    CHECK_EQUAL_INT(expected_alu, alu_result, "ALU Add operation failed.");
    CHECK_TRUE(fabsf(fpu_result - expected_fpu) < FLOAT_TOLERANCE, "FPU Add operation failed.");

    // Print results
    PRINT_RESULT("Mixed ALU and FPU Operations",
                "Computed", "Expected", "Result");

    char alu_res_str[25];
    int_to_str(alu_result, alu_res_str);
    char expected_alu_str[25];
    int_to_str(expected_alu, expected_alu_str);
    PRINT_RESULT("ALU Add", alu_res_str, expected_alu_str, (alu_result == expected_alu) ? "PASS" : "FAIL");

    char fpu_res_str[25];
    float_to_str(fpu_result, fpu_res_str, 6);
    char expected_fpu_str[25];
    float_to_str(expected_fpu, expected_fpu_str, 6);
    PRINT_RESULT("FPU Add", fpu_res_str, expected_fpu_str, (fabsf(fpu_result - expected_fpu) < FLOAT_TOLERANCE) ? "PASS" : "FAIL");
}

// Scenario 5: Branch and Jump Instructions
void test_branch_jump() {
    PRINT_HEADER();
    printf("Testing Branch and Jump Instructions...\n");

    // Initialize loop counter
    volatile uint32_t loop_counter = 0;
    volatile uint32_t target = 5;

    // Inline assembly to implement a loop with branches
    asm volatile (
        "mv t0, x0 \n\t"        // Initialize loop counter to 0
        "mv t1, %[max] \n\t"    // Move max value into t1

        "loop_label: \n\t"
        "addi t0, t0, 1 \n\t"   // Increment counter
        "blt t0, t1, loop_label \n\t"  // Branch if t0 < t1
        "mv %[counter], t0 \n\t"       // Move t0 to loop_counter
        : [counter] "=r" (loop_counter)
        : [max] "r" (target)
        : "t0", "t1"
    );

    // Expected result
    uint32_t expected = target;

    // Verify loop counter
    CHECK_EQUAL_INT(expected, loop_counter, "Branch loop failed.");

    // Print result
    PRINT_RESULT("Branch and Jump Instructions",
                "Computed", "Expected", "Result");

    char counter_str[25];
    int_to_str(loop_counter, counter_str);
    char expected_str[25];
    int_to_str(expected, expected_str);

    PRINT_RESULT("Branch Loop", counter_str, expected_str, (loop_counter == expected) ? "PASS" : "FAIL");
}

// Scenario 6: Memory Access Contention
void test_memory_access_contention() {
    PRINT_HEADER();
    printf("Testing Memory Access Contention...\n");

    // Initialize memory locations
    memory_a = 100;
    memory_b = 200;

    // Perform overlapping load and store operations
    asm volatile (
        "lw t0, 0(%[pa]) \n\t" // Load from memory_a
        "lw t1, 0(%[pb]) \n\t" // Load from memory_b
        "sw t0, 0(%[pb]) \n\t" // Store to memory_b
        "sw t1, 0(%[pa]) \n\t" // Store to memory_a
        :
        : [pa] "r" (&memory_a),
          [pb] "r" (&memory_b)
        : "t0", "t1"
    );

    // Expected results: memory_a and memory_b swapped
    uint32_t expected_a = 200;
    uint32_t expected_b = 100;

    // Verify memory contents
    CHECK_EQUAL_INT(expected_a, memory_a, "Memory_a after swap failed.");
    CHECK_EQUAL_INT(expected_b, memory_b, "Memory_b after swap failed.");

    // Print results
    PRINT_RESULT("Memory Access Contention",
                "Computed", "Expected", "Result");

    char memory_a_str[25], memory_b_str[25];
    int_to_str(memory_a, memory_a_str);
    int_to_str(memory_b, memory_b_str);
    char expected_a_str[25], expected_b_str[25];
    int_to_str(expected_a, expected_a_str);
    int_to_str(expected_b, expected_b_str);

    PRINT_RESULT("Memory Swap a", memory_a_str, expected_a_str, (memory_a == expected_a) ? "PASS" : "FAIL");
    PRINT_RESULT("Memory Swap b", memory_b_str, expected_b_str, (memory_b == expected_b) ? "PASS" : "FAIL");
}

// Scenario 7: FPU and Memory Access Contention
void test_fpu_memory_contention() {
    PRINT_HEADER();
    printf("Testing FPU and Memory Access Contention...\n");

    // Initialize variables
    float fa = 1.0f, fb = 2.0f;
    volatile uint32_t mem_val = 50;
    float fpu_result;
    uint32_t loaded_val;

    // Perform FPU and memory operations together
    asm volatile (
        "fadd.s %[fpu_res], %[a], %[b] \n\t" // FPU add
        "lw %[loaded], 0(%[pmem]) \n\t"     // Load from memory
        : [fpu_res] "=f" (fpu_result),
          [loaded] "=r" (loaded_val)
        : [a] "f" (fa),
          [b] "f" (fb),
          [pmem] "r" (&mem_val)
    );

    // Expected results
    float expected_fpu = fa + fb; // 3.0f
    uint32_t expected_loaded = mem_val; // 50

    // Verify results using local float comparison for FPU
    CHECK_TRUE(fabsf(fpu_result - expected_fpu) < FLOAT_TOLERANCE, "FPU Add operation failed.");
    CHECK_EQUAL_INT(expected_loaded, loaded_val, "Load from memory failed.");

    // Print results
    PRINT_RESULT("FPU and Memory Access Contention",
                "Computed", "Expected", "Result");

    char fpu_res_str[25], loaded_val_str[25];
    float_to_str(fpu_result, fpu_res_str, 6);
    int_to_str(loaded_val, loaded_val_str);
    char expected_fpu_str[25], expected_loaded_str[25];
    float_to_str(expected_fpu, expected_fpu_str, 6);
    int_to_str(expected_loaded, expected_loaded_str);

    PRINT_RESULT("FPU Add", fpu_res_str, expected_fpu_str, (fabsf(fpu_result - expected_fpu) < FLOAT_TOLERANCE) ? "PASS" : "FAIL");
    PRINT_RESULT("Memory Load", loaded_val_str, expected_loaded_str, (loaded_val == expected_loaded) ? "PASS" : "FAIL");
}

// Main Test Execution Function
int main() {
    printf("Starting Structural Hazards Test on RISC-V 64 CPU...\n");

    testcase_init();

    // Execute all test scenarios
    test_alu_contention();
    test_load_store_contention();
    test_fpu_contention();
    test_mixed_alu_fpu();
    test_branch_jump();
    test_memory_access_contention();
    test_fpu_memory_contention();

    // Finalize test and get result
    int final_result = testcase_finalize();

    if (final_result == TEST_SUCCESS) {
        printf("All Structural Hazards Tests Passed Successfully!\n");
        return 0; // Success
    } else {
        printf("Some Structural Hazards Tests Failed.\n");
        return 1; // Failure
    }

}
