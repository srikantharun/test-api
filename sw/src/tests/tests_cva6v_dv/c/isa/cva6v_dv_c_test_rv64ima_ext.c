// This is a test file for rv64ima_ext
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test RV64IMA extensions: RV64I, RV64M, and RV64A
// This function tests various arithmetic, multiplication, and atomic operations
void test_rv64ima_ext() {
    uint64_t registers[32];
    uint64_t result;

    // Initialize the registers with non-zero values
    initialize_registers();

    // Print starting message
    printf("Testing RV64IMA Extensions...\n");

    // RV64I: Basic arithmetic operations
    // Test addition and subtraction
    for (int i = 1; i < 32; i++) {
        result = registers[i] + registers[i - 1];
        printf("ADD x%d, x%d: %lu + %lu = %lu\n", i, i - 1, registers[i], registers[i - 1], result);

        result = registers[i] - registers[i - 1];
        printf("SUB x%d, x%d: %lu - %lu = %lu\n", i, i - 1, registers[i], registers[i - 1], result);
    }

    // RV64M: Multiplication and division operations
    // Test multiplication, division, and modulus
    for (int i = 1; i < 32; i++) {
        result = registers[i] * registers[i - 1];
        printf("MUL x%d, x%d: %lu * %lu = %lu\n", i, i - 1, registers[i], registers[i - 1], result);

        if (registers[i - 1] != 0) {
            result = registers[i] / registers[i - 1];
            printf("DIV x%d, x%d: %lu / %lu = %lu\n", i, i - 1, registers[i], registers[i - 1], result);

            result = registers[i] % registers[i - 1];
            printf("REM x%d, x%d: %lu %% %lu = %lu\n", i, i - 1, registers[i], registers[i - 1], result);
        } else {
            printf("DIV x%d, x%d: Division by zero error\n", i, i - 1);
            printf("REM x%d, x%d: Modulus by zero error\n", i, i - 1);
        }
    }

    // RV64A: Atomic operations (assuming memory addresses 0x1000 and 0x1008 for demonstration)
    uint64_t *mem = (uint64_t *)0x1000;
    *mem = 42;
    uint64_t *mem2 = (uint64_t *)0x1008;
    *mem2 = 84;

    uint64_t loaded_value;
    uint64_t swapped_value = 128;

    // Atomic load-reserved and store-conditional (LR/SC)
    __asm__ volatile (
        "lr.d %0, (%1)\n"
        "sc.d %2, %3, (%1)\n"
        : "=r"(loaded_value), "=r"(*mem), "=r"(result)
        : "r"(swapped_value)
        : "memory"
    );
    printf("LR/SC: Loaded value = %lu, Store conditional result = %lu\n", loaded_value, result);

    // Atomic memory operations (AMO)
    uint64_t amo_result;
    uint64_t amo_operand = 21;

    __asm__ volatile (
        "amoadd.d %0, %2, (%1)\n"
        : "=r"(amo_result)
        : "r"(mem), "r"(amo_operand)
        : "memory"
    );
    printf("AMOADD: Result = %lu, Memory = %lu\n", amo_result, *mem);

    // Completion message
    printf("RV64IMA Extensions Test Completed.\n");
}

int main() {
    printf("Running test: rv64ima_ext\n");
    initialize_registers();
    test_rv64ima_ext();
    return 0;
}
