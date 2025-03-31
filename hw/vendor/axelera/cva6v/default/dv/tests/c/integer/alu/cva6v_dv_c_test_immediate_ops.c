// This is a test file for immediate_ops
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test immediate arithmetic and logical operations
void test_immediate_ops() {
    // Initialize source register values
    int64_t rs1 = (rand() % 100) - 50;  // Random value between -50 and 49
    int64_t result, expected;

    // ADDI (Add Immediate)
    __asm__ volatile (
        "addi %0, %1, 5\n"  // result = rs1 + 5
        : "=r"(result)
        : "r"(rs1)
    );
    expected = rs1 + 5;
    printf("ADDI: Expected = %ld, Result = %ld\n", expected, result);

    // SLTI (Set Less Than Immediate)
    __asm__ volatile (
        "slti %0, %1, 15\n"  // result = (rs1 < 15) ? 1 : 0
        : "=r"(result)
        : "r"(rs1)
    );
    expected = (rs1 < 15) ? 1 : 0;
    printf("SLTI: Expected = %ld, Result = %ld\n", expected, result);

    // ANDI (AND Immediate)
    __asm__ volatile (
        "andi %0, %1, 7\n"  // result = rs1 & 7
        : "=r"(result)
        : "r"(rs1)
    );
    expected = rs1 & 7;
    printf("ANDI: Expected = %ld, Result = %ld\n", expected, result);

    // ORI (OR Immediate)
    __asm__ volatile (
        "ori %0, %1, 3\n"  // result = rs1 | 3
        : "=r"(result)
        : "r"(rs1)
    );
    expected = rs1 | 3;
    printf("ORI: Expected = %ld, Result = %ld\n", expected, result);

    // XORI (XOR Immediate)
    __asm__ volatile (
        "xori %0, %1, 12\n"  // result = rs1 ^ 12
        : "=r"(result)
        : "r"(rs1)
    );
    expected = rs1 ^ 12;
    printf("XORI: Expected = %ld, Result = %ld\n", expected, result);

    // LUI (Load Upper Immediate)
    __asm__ volatile (
        "lui %0, 0x12345\n"  // result = 0x12345 << 12
        : "=r"(result)
    );
    expected = 0x12345 << 12;
    printf("LUI: Expected = 0x%lx, Result = 0x%lx\n", expected, result);

    // AUIPC (Add Upper Immediate to PC)
    __asm__ volatile (
        "auipc %0, 0x10\n"  // result = PC + (0x10 << 12)
        : "=r"(result)
    );
    // Note: AUIPC test requires knowledge of current PC; the expected result is
    // not straightforward to determine without fetching the PC value.
    printf("AUIPC: Result = 0x%lx (Expected: PC + 0x10000)\n", result);

    // ADDIW (Add Immediate Word)
    __asm__ volatile (
        "addiw %0, %1, 5\n"  // result = (int32_t)rs1 + 5
        : "=r"(result)
        : "r"(rs1)
    );
    expected = (int32_t)rs1 + 5;
    printf("ADDIW: Expected = %d, Result = %d\n", (int32_t)expected, (int32_t)result);

    // SLLIW (Shift Left Logical Immediate Word)
    __asm__ volatile (
        "slliw %0, %1, 2\n"  // result = (int32_t)rs1 << 2
        : "=r"(result)
        : "r"(rs1)
    );
    expected = (int32_t)rs1 << 2;
    printf("SLLIW: Expected = %d, Result = %d\n", (int32_t)expected, (int32_t)result);

    // SRLIW (Shift Right Logical Immediate Word)
    __asm__ volatile (
        "srliw %0, %1, 2\n"  // result = (uint32_t)rs1 >> 2
        : "=r"(result)
        : "r"(rs1)
    );
    expected = (uint32_t)rs1 >> 2;
    printf("SRLIW: Expected = %u, Result = %u\n", (uint32_t)expected, (uint32_t)result);

    // SRAIW (Shift Right Arithmetic Immediate Word)
    __asm__ volatile (
        "sraiw %0, %1, 2\n"  // result = (int32_t)rs1 >> 2
        : "=r"(result)
        : "r"(rs1)
    );
    expected = (int32_t)rs1 >> 2;
    printf("SRAIW: Expected = %d, Result = %d\n", (int32_t)expected, (int32_t)result);
}

int main() {
    printf("Running test: immediate_ops\n");
    srand(get_time());  // Initialize random seed
    initialize_registers();
    test_immediate_ops();
    return 0;
}
