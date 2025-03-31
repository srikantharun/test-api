// This is a test file for imm_enc_variants
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test I-type immediate encoding
void test_i_type_imm(uint64_t *regs) {
    uint64_t result;

    // Example I-type instruction: ADDI with immediate value 10
    __asm__ volatile (
        "addi %0, %1, 10\n"
        : "=r"(result)
        : "r"(regs[1])
    );
    printf("I-type ADDI: x1 + 10 = %lu\n", result);

    // Example I-type instruction: ANDI with immediate value 15
    __asm__ volatile (
        "andi %0, %1, 15\n"
        : "=r"(result)
        : "r"(regs[2])
    );
    printf("I-type ANDI: x2 & 15 = %lu\n", result);
}

// Function to test S-type immediate encoding
void test_s_type_imm(uint64_t *regs, uint64_t *memory) {
    // Example S-type instruction: SW (Store Word) with offset 4
    __asm__ volatile (
        "sw %1, 4(%0)\n"
        :
        : "r"(&memory[0]), "r"(regs[3])
    );
    printf("S-type SW: memory[1] = %lu\n", memory[1]);

    // Example S-type instruction: SH (Store Halfword) with offset 6
    __asm__ volatile (
        "sh %1, 6(%0)\n"
        :
        : "r"(&memory[0]), "r"(regs[4])
    );
    printf("S-type SH: memory[3] = %lu\n", ((uint16_t*)memory)[3]);
}

// Function to test B-type immediate encoding
void test_b_type_imm(uint64_t *regs) {
    uint64_t result = 0;

    // Example B-type instruction: BEQ with offset 4
    __asm__ volatile (
        "beq %1, %2, 1f\n"
        "addi %0, %0, 1\n"
        "1:\n"
        : "=r"(result)
        : "r"(regs[5]), "r"(regs[6]), "0"(result)
    );
    printf("B-type BEQ: result = %lu\n", result);

    // Example B-type instruction: BNE with offset 8
    __asm__ volatile (
        "bne %1, %2, 1f\n"
        "addi %0, %0, 1\n"
        "1:\n"
        : "=r"(result)
        : "r"(regs[7]), "r"(regs[8]), "0"(result)
    );
    printf("B-type BNE: result = %lu\n", result);
}

void test_imm_enc_variants() {
    uint64_t registers[32];
    uint64_t memory[32];

    // Initialize registers and memory
    initialize_registers();
    for (int i = 0; i < 32; i++) {
        memory[i] = 0;
    }

    // Print starting message
    printf("Testing Immediate Encoding Variants...\n");

    // Test I-type immediate encoding
    test_i_type_imm(registers);

    // Test S-type immediate encoding
    test_s_type_imm(registers, memory);

    // Test B-type immediate encoding
    test_b_type_imm(registers);

    // Print completion message
    printf("Immediate  Encoding Variants...\n");

    // Test I-type immediate encoding
    test_i_type_imm(registers);

    // Test S-type immediate encoding
    test_s_type_imm(registers, memory);

    // Test B-type immediate encoding
    test_b_type_imm(registers);

    // Print completion message
    printf("Immediate Encoding Variants Test Completed.\n");
}

int main() {
    printf("Running test: imm_enc_variants\n");
    initialize_registers();
    test_imm_enc_variants();
    return 0;
}
