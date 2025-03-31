// This is a test file for int_comp_instr_rvc
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test RISC-V Compressed (RVC) integer computational instructions
void test_int_comp_instr_rvc() {
    uint64_t result;
    int32_t expected;
    int32_t a = (int32_t)rand();
    int32_t b = (int32_t)rand();

    // Test c.addi (compressed add immediate)
    __asm__ volatile("c.addi %0, %1, 5" : "=r"(result) : "r"(a));
    expected = a + 5;
    printf("c.addi: %d + 5 = %d, Expected: %d %s\n", a, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.addiw (compressed add immediate word)
    __asm__ volatile("c.addiw %0, %1, 5" : "=r"(result) : "r"(a));
    expected = (int32_t)(a + 5);
    printf("c.addiw: %d + 5 = %d, Expected: %d %s\n", a, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.add (compressed add)
    __asm__ volatile("c.add %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
    expected = a + b;
    printf("c.add: %d + %d = %d, Expected: %d %s\n", a, b, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.sub (compressed subtract)
    __asm__ volatile("c.sub %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
    expected = a - b;
    printf("c.sub: %d - %d = %d, Expected: %d %s\n", a, b, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.and (compressed bitwise AND)
    __asm__ volatile("c.and %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
    expected = a & b;
    printf("c.and: %d & %d = %d, Expected: %d %s\n", a, b, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.or (compressed bitwise OR)
    __asm__ volatile("c.or %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
    expected = a | b;
    printf("c.or: %d | %d = %d, Expected: %d %s\n", a, b, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.xor (compressed bitwise XOR)
    __asm__ volatile("c.xor %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
    expected = a ^ b;
    printf("c.xor: %d ^ %d = %d, Expected: %d %s\n", a, b, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.li (compressed load immediate)
    __asm__ volatile("c.li %0, 5" : "=r"(result));
    expected = 5;
    printf("c.li: li = %d, Expected: %d %s\n", (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.lui (compressed load upper immediate)
    __asm__ volatile("c.lui %0, 0x12345" : "=r"(result));
    expected = 0x12345000;
    printf("c.lui: lui = %x, Expected: %x %s\n", (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.slli (compressed shift left logical immediate)
    __asm__ volatile("c.slli %0, %1, 3" : "=r"(result) : "r"(a));
    expected = a << 3;
    printf("c.slli: %d << 3 = %d, Expected: %d %s\n", a, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.srli (compressed shift right logical immediate)
    __asm__ volatile("c.srli %0, %1, 3" : "=r"(result) : "r"(a));
    expected = (uint32_t)a >> 3;
    printf("c.srli: %u >> 3 = %u, Expected: %u %s\n", a, (uint32_t)result, (uint32_t)expected, (uint32_t)result == (uint32_t)expected ? "PASS" : "FAIL");

    // Test c.srai (compressed shift right arithmetic immediate)
    __asm__ volatile("c.srai %0, %1, 3" : "=r"(result) : "r"(a));
    expected = a >> 3;
    printf("c.srai: %d >> 3 = %d, Expected: %d %s\n", a, (int32_t)result, expected, result == expected ? "PASS" : "FAIL");
}

int main() {
    printf("Running test: int_comp_instr_rvc\n");
    initialize_registers();
    test_int_comp_instr_rvc();
    return 0;
}
