// This is a test file for hint_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test HINT instructions
void test_hint_instrc() {
    // Print starting message
    printf("Testing HINT Instructions...\n");

    // Initialize registers for testing
    uint64_t rd = 0, rs1 = 1, result;

    // Test LUI (Load Upper Immediate) instruction
    // This instruction loads an immediate value into the upper 20 bits of the destination register
    __asm__ volatile (
        "lui %0, 0x12345\n"
        : "=r"(result)
    );
    printf("LUI: rd=0x%lx Expected=0x12345000 Result=0x%lx %s\n", rd, result, (result == 0x12345000) ? "PASS" : "FAIL");

    // Test AUIPC (Add Upper Immediate to PC) instruction
    // This instruction computes the address PC + imm and stores it in the destination register
    __asm__ volatile (
        "auipc %0, 0x12345\n"
        : "=r"(result)
    );
    // The expected value will be PC + (0x12345 << 12)
    printf("AUIPC: rd=0x%lx Result=0x%lx\n", rd, result); // Since PC is unknown, we print the result directly

    // Test ADDI (Add Immediate) instruction
    // This instruction adds an immediate value to the source register and stores the result in the destination register
    __asm__ volatile (
        "addi %0, %1, 10\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("ADDI: rd=0x%lx rs1=0x%lx Immediate=10 Result=0x%lx\n", rd, rs1, result);

    // Test ANDI (AND Immediate) instruction
    // This instruction performs a bitwise AND between the source register and an immediate value, storing the result in the destination register
    __asm__ volatile (
        "andi %0, %1, 0xF\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("ANDI: rd=0x%lx rs1=0x%lx Immediate=0xF Result=0x%lx\n", rd, rs1, result);

    // Test ORI (OR Immediate) instruction
    // This instruction performs a bitwise OR between the source register and an immediate value, storing the result in the destination register
    __asm__ volatile (
        "ori %0, %1, 0xF\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("ORI: rd=0x%lx rs1=0x%lx Immediate=0xF Result=0x%lx\n", rd, rs1, result);

    // Test XORI (XOR Immediate) instruction
    // This instruction performs a bitwise XOR between the source register and an immediate value, storing the result in the destination register
    __asm__ volatile (
        "xori %0, %1, 0xF\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("XORI: rd=0x%lx rs1=0x%lx Immediate=0xF Result=0x%lx\n", rd, rs1, result);

    // Test ADDIW (Add Immediate Word) instruction
    // This instruction adds a sign-extended immediate value to a 32-bit value from the source register, storing the result in the destination register
    __asm__ volatile (
        "addiw %0, %1, 10\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("ADDIW: rd=0x%lx rs1=0x%lx Immediate=10 Result=0x%lx\n", rd, rs1, result);

    // Test SLLIW (Shift Left Logical Immediate Word) instruction
    // This instruction shifts a 32-bit value from the source register left by an immediate value, storing the result in the destination register
    __asm__ volatile (
        "slliw %0, %1, 2\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("SLLIW: rd=0x%lx rs1=0x%lx Immediate=2 Result=0x%lx\n", rd, rs1, result);

    // Test SRLIW (Shift Right Logical Immediate Word) instruction
    // This instruction shifts a 32-bit value from the source register right by an immediate value, storing the result in the destination register
    __asm__ volatile (
        "srliw %0, %1, 2\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("SRLIW: rd=0x%lx rs1=0x%lx Immediate=2 Result=0x%lx\n", rd, rs1, result);

    // Test SRAIW (Shift Right Arithmetic Immediate Word) instruction
    // This instruction shifts a 32-bit value from the source register right by an immediate value with sign extension, storing the result in the destination register
    __asm__ volatile (
        "sraiw %0, %1, 2\n"
        : "=r"(result)
        : "r"(rs1)
    );
    printf("SRAIW: rd=0x%lx rs1=0x%lx Immediate=2 Result=0x%lx\n", rd, rs1, result);

    // Completion message
    printf("HINT Instructions Test Completed.\n");
}


int main() {
    printf("Running test: hint_instr\n");
    initialize_registers();
    test_hint_instrc();
    return 0;
}
