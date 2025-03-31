// This is a test file for accrued_exception_flags
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test accrued exception flags
void test_accured_exception_flags() {
    float a = 1.0f, b = 0.0f;
    float result;
    uint32_t fflags;
    char hex_str_a[9], hex_str_b[9], hex_str_result[9];

    // Clear all exception flags
    __asm__ volatile("csrw fflags, zero");

    // Test for invalid operation (nv)
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(b), "f"(b));
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("nv: 0.0 / 0.0 = 0x%s, fflags = 0x%x (Expected: 0x10) %s\n", hex_str_result, fflags, (fflags & 0x10) ? "PASS" : "FAIL");

    // Clear all exception flags
    __asm__ volatile("csrw fflags, zero");

    // Test for divide by zero (dz)
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("dz: 1.0 / 0.0 = 0x%s, fflags = 0x%x (Expected: 0x08) %s\n", hex_str_result, fflags, (fflags & 0x08) ? "PASS" : "FAIL");

    // Clear all exception flags
    __asm__ volatile("csrw fflags, zero");

    // Test for overflow (of)
    a = 3.4e38f;
    b = 3.4e38f;
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(float_to_bits(a), hex_str_a);
    int_to_hex(float_to_bits(b), hex_str_b);
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("of: 0x%s + 0x%s = 0x%s, fflags = 0x%x (Expected: 0x04) %s\n", hex_str_a, hex_str_b, hex_str_result, fflags, (fflags & 0x04) ? "PASS" : "FAIL");

    // Clear all exception flags
    __asm__ volatile("csrw fflags, zero");

    // Test for underflow (uf)
    a = 1e-38f;
    b = 1e-38f;
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(float_to_bits(a), hex_str_a);
    int_to_hex(float_to_bits(b), hex_str_b);
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("uf: 0x%s * 0x%s = 0x%s, fflags = 0x%x (Expected: 0x02) %s\n", hex_str_a, hex_str_b, hex_str_result, fflags, (fflags & 0x02) ? "PASS" : "FAIL");

    // Clear all exception flags
    __asm__ volatile("csrw fflags, zero");

    // Test for inexact (nx)
    a = 1.0f / 3.0f;
    b = 1.0f;
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(float_to_bits(a), hex_str_a);
    int_to_hex(float_to_bits(b), hex_str_b);
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("nx: 0x%s + 0x%s = 0x%s, fflags = 0x%x (Expected: 0x01) %s\n", hex_str_a, hex_str_b, hex_str_result, fflags, (fflags & 0x01) ? "PASS" : "FAIL");
}

int main() {
    printf("Running test: accured_exception_flags\n");
    initialize_registers();
    test_accured_exception_flags();
    return 0;
}
