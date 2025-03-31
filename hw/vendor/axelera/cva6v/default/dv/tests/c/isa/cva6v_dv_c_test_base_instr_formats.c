// This is a test file for base_instr_formats
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test R-type instructions
void test_r_type(uint64_t *regs) {
    uint64_t result;

    // Example R-type instruction: ADD
    __asm__ volatile (
        "add %0, %1, %2\n"
        : "=r"(result)
        : "r"(regs[1]), "r"(regs[2])
    );
    printf("R-type ADD: x1 + x2 = %lu\n", result);

    // Example R-type instruction: SUB
    __asm__ volatile (
        "sub %0, %1, %2\n"
        : "=r"(result)
        : "r"(regs[3]), "r"(regs[4])
    );
    printf("R-type SUB: x3 - x4 = %lu\n", result);
}

// Function to test I-type instructions
void test_i_type(uint64_t *regs) {
    uint64_t result;

    // Example I-type instruction: ADDI
    __asm__ volatile (
        "addi %0, %1, 10\n"
        : "=r"(result)
        : "r"(regs[5])
    );
    printf("I-type ADDI: x5 + 10 = %lu\n", result);

    // Example I-type instruction: ANDI
    __asm__ volatile (
        "andi %0, %1, 15\n"
        : "=r"(result)
        : "r"(regs[6])
    );
    printf("I-type ANDI: x6 & 15 = %lu\n", result);
}

// Function to test S-type instructions
void test_s_type(uint64_t *regs, uint64_t *memory) {
    // Example S-type instruction: SW (Store Word)
    __asm__ volatile (
        "sw %1, 0(%0)\n"
        :
        : "r"(&memory[0]), "r"(regs[7])
    );
    printf("S-type SW: memory[0] = %lu\n", memory[0]);

    // Example S-type instruction: SH (Store Halfword)
    __asm__ volatile (
        "sh %1, 2(%0)\n"
        :
        : "r"(&memory[0]), "r"(regs[8])
    );
    printf("S-type SH: memory[1] = %lu\n", ((uint16_t*)memory)[1]);
}

// Function to test B-type instructions
void test_b_type(uint64_t *regs) {
    uint64_t result = 0;

    // Example B-type instruction: BEQ
    __asm__ volatile (
        "beq %1, %2, 1f\n"
        "addi %0, %0, 1\n"
        "1:\n"
        : "=r"(result)
        : "r"(regs[9]), "r"(regs[10]), "0"(result)
    );
    printf("B-type BEQ: result = %lu\n", result);

    // Example B-type instruction: BNE
    __asm__ volatile (
        "bne %1, %2, 1f\n"
        "addi %0, %0, 1\n"
        "1:\n"
        : "=r"(result)
        : "r"(regs[11]), "r"(regs[12]), "0"(result)
    );
    printf("B-type BNE: result = %lu\n", result);
}

// Function to test U-type instructions
void test_u_type() {
    uint64_t result;

    // Example U-type instruction: LUI
    __asm__ volatile (
        "lui %0, 0x12345\n"
        : "=r"(result)
    );
    printf("U-type LUI: result = %lu\n", result);

    // Example U-type instruction: AUIPC
    __asm__ volatile (
        "auipc %0, 0x12345\n"
        : "=r"(result)
    );
    printf("U-type AUIPC: result = %lu\n", result);
}

// Function to test J-type instructions
void test_j_type() {
    uint64_t result = 0;

    // Example J-type instruction: JAL
    __asm__ volatile (
        "jal %0, 1f\n"
        "addi %0, %0, 1\n"
        "1:\n"
        : "=r"(result)
    );
    printf("J-type JAL: result = %lu\n", result);

    // Example J-type instruction: JALR
    __asm__ volatile (
        "jalr %0, %1, 0\n"
        "addi %0, %0, 1\n"
        : "=r"(result)
        : "r"(result)
    );
    printf("J-type JALR: result = %lu\n", result);
}

void test_base_instr_formats() {
    uint64_t registers[32];
    uint64_t memory[32];

    // Initialize registers and memory
    initialize_registers();
    for (int i = 0; i < 32; i++) {
        memory[i] = 0;
    }

    // Print starting message
    printf("Testing Base Instruction Formats...\n");

    // Test R-type instructions
    test_r_type(registers);

    // Test I-type instructions
    test_i_type(registers);

    // Test S-type instructions
    test_s_type(registers, memory);

    // Test B-type instructions
    test_b_type(registers);

    // Test U-type instructions
    test_u_type();

    // Test J-type instructions
    test_j_type();

    // Print completion message
    printf("Base Instruction Formats Test Completed.\n");
}

int main() {
    printf("Running test: base_instr_formats\n");
    initialize_registers();
    test_base_instr_formats();
    return 0;
}
