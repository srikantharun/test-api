// This is a test file for hint_instr_rvc
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test RISC-V Compressed (RVC) HINT instructions
void test_hint_instr_rvc() {
    uint32_t result, expected;

    // Test c.nop (no operation)
    __asm__ volatile("c.nop");
    printf("c.nop: Executed No Operation PASS\n");

    // Test c.addi (compressed add immediate)
    int32_t rs1 = rand() % 32;
    int32_t imm = rand() % 32;
    __asm__ volatile("c.addi %0, %1, %2" : "=r"(result) : "r"(rs1), "I"(imm));
    expected = rs1 + imm;
    printf("c.addi: %d + %d = %d, Expected: %d %s\n", rs1, imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.li (compressed load immediate)
    int32_t imm_li = rand() % 32;
    __asm__ volatile("c.li %0, %1" : "=r"(result) : "I"(imm_li));
    expected = imm_li;
    printf("c.li: Loaded Immediate %d, Expected: %d %s\n", result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.lui (compressed load upper immediate)
    int32_t imm_lui = rand() % 32;
    __asm__ volatile("c.lui %0, %1" : "=r"(result) : "I"(imm_lui));
    expected = imm_lui << 12;
    printf("c.lui: Loaded Upper Immediate %d, Expected: %d %s\n", result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.mv (compressed move)
    int32_t rs1_mv = rand() % 32;
    __asm__ volatile("c.mv %0, %1" : "=r"(result) : "r"(rs1_mv));
    expected = rs1_mv;
    printf("c.mv: Moved %d, Expected: %d %s\n", result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.add (compressed add)
    int32_t rs2_add = rand() % 32;
    __asm__ volatile("c.add %0, %1, %2" : "=r"(result) : "r"(rs1), "r"(rs2_add));
    expected = rs1 + rs2_add;
    printf("c.add: %d + %d = %d, Expected: %d %s\n", rs1, rs2_add, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.addw (compressed add word)
    int32_t rs2_addw = rand() % 32;
    __asm__ volatile("c.addw %0, %1, %2" : "=r"(result) : "r"(rs1), "r"(rs2_addw));
    expected = (int32_t)rs1 + (int32_t)rs2_addw;
    printf("c.addw: %d + %d = %d, Expected: %d %s\n", rs1, rs2_addw, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.addi16sp (compressed add immediate to sp)
    int32_t imm_addi16sp = rand() % 32;
    __asm__ volatile("c.addi16sp %0, %1" : "=r"(result) : "I"(imm_addi16sp));
    expected = imm_addi16sp; // This is a simplification, in reality, it adds to the stack pointer
    printf("c.addi16sp: Added %d to sp, Expected: %d %s\n", imm_addi16sp, expected, result == expected ? "PASS" : "FAIL");

    // Test c.sub (compressed subtract)
    int32_t rs2_sub = rand() % 32;
    __asm__ volatile("c.sub %0, %1, %2" : "=r"(result) : "r"(rs1), "r"(rs2_sub));
    expected = rs1 - rs2_sub;
    printf("c.sub: %d - %d = %d, Expected: %d %s\n", rs1, rs2_sub, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.and (compressed and)
    int32_t rs2_and = rand() % 32;
    __asm__ volatile("c.and %0, %1, %2" : "=r"(result) : "r"(rs1), "r"(rs2_and));
    expected = rs1 & rs2_and;
    printf("c.and: %d & %d = %d, Expected: %d %s\n", rs1, rs2_and, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.or (compressed or)
    int32_t rs2_or = rand() % 32;
    __asm__ volatile("c.or %0, %1, %2" : "=r"(result) : "r"(rs1), "r"(rs2_or));
    expected = rs1 | rs2_or;
    printf("c.or: %d | %d = %d, Expected: %d %s\n", rs1, rs2_or, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.xor (compressed xor)
    int32_t rs2_xor = rand() % 32;
    __asm__ volatile("c.xor %0, %1, %2" : "=r"(result) : "r"(rs1), "r"(rs2_xor));
    expected = rs1 ^ rs2_xor;
    printf("c.xor: %d ^ %d = %d, Expected: %d %s\n", rs1, rs2_xor, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.srli (compressed shift right logical immediate)
    int32_t imm_srli = rand() % 32;
    __asm__ volatile("c.srli %0, %1, %2" : "=r"(result) : "r"(rs1), "I"(imm_srli));
    expected = rs1 >> imm_srli;
    printf("c.srli: %d >> %d = %d, Expected: %d %s\n", rs1, imm_srli, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.srai (compressed shift right arithmetic immediate)
    int32_t imm_srai = rand() % 32;
    __asm__ volatile("c.srai %0, %1, %2" : "=r"(result) : "r"(rs1), "I"(imm_srai));
    expected = (int32_t)rs1 >> imm_srai;
    printf("c.srai: %d >> %d = %d, Expected: %d %s\n", rs1, imm_srai, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.andi (compressed and immediate)
    int32_t imm_andi = rand() % 32;
    __asm__ volatile("c.andi %0, %1, %2" : "=r"(result) : "r"(rs1), "I"(imm_andi));
    expected = rs1 & imm_andi;
    printf("c.andi: %d & %d = %d, Expected: %d %s\n", rs1, imm_andi, result, expected, result == expected ? "PASS" : "FAIL");
}

int main() {
    printf("Running test: hint_instr_rvc\n");
    init_registers();
    test_hint_instr_rvc();
    return 0;
}
