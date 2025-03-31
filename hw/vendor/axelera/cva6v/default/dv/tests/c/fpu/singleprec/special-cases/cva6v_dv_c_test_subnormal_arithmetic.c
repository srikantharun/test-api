// This is a test file for subnormal_arithmetic
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test subnormal arithmetic operations
void test_subnormal_arithmetic() {
    // Subnormal numbers are very small numbers represented with reduced precision.
    // These tests will verify if the subnormal numbers are handled correctly.

    // Define subnormal numbers
    float subnormal1 = 1.4e-45f; // Smallest positive subnormal number
    float subnormal2 = 2.8e-45f; // Another small subnormal number
    float normal = 1.0f;         // Normal number for comparison
    float result, expected;

    // Test addition with subnormal numbers
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(subnormal1), "f"(subnormal2));
    expected = subnormal1 + subnormal2;
    printf("fadd.s (Subnormal): %e + %e = %e, Expected: %e %s\n", subnormal1, subnormal2, result, expected, result == expected ? "PASS" : "FAIL");

    // Test subtraction with subnormal numbers
    __asm__ volatile("fsub.s %0, %1, %2" : "=f"(result) : "f"(subnormal2), "f"(subnormal1));
    expected = subnormal2 - subnormal1;
    printf("fsub.s (Subnormal): %e - %e = %e, Expected: %e %s\n", subnormal2, subnormal1, result, expected, result == expected ? "PASS" : "FAIL");

    // Test multiplication with subnormal numbers
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(subnormal1), "f"(normal));
    expected = subnormal1 * normal;
    printf("fmul.s (Subnormal): %e * %f = %e, Expected: %e %s\n", subnormal1, normal, result, expected, result == expected ? "PASS" : "FAIL");

    // Test division with subnormal numbers
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(subnormal2), "f"(normal));
    expected = subnormal2 / normal;
    printf("fdiv.s (Subnormal): %e / %f = %e, Expected: %e %s\n", subnormal2, normal, result, expected, result == expected ? "PASS" : "FAIL");

    // Test square root of a subnormal number
    __asm__ volatile("fsqrt.s %0, %1" : "=f"(result) : "f"(subnormal1));
    expected = sqrtf(subnormal1);
    printf("fsqrt.s (Subnormal): sqrt(%e) = %e, Expected: %e %s\n", subnormal1, result, expected, result == expected ? "PASS" : "FAIL");

    // Test minimum with a subnormal number and a normal number
    __asm__ volatile("fmin.s %0, %1, %2" : "=f"(result) : "f"(subnormal1), "f"(normal));
    expected = fminf(subnormal1, normal);
    printf("fmin.s (Subnormal): fmin(%e, %f) = %e, Expected: %e %s\n", subnormal1, normal, result, expected, result == expected ? "PASS" : "FAIL");

    // Test maximum with a subnormal number and a normal number
    __asm__ volatile("fmax.s %0, %1, %2" : "=f"(result) : "f"(subnormal1), "f"(normal));
    expected = fmaxf(subnormal1, normal);
    printf("fmax.s (Subnormal): fmax(%e, %f) = %e, Expected: %e %s\n", subnormal1, normal, result, expected, result == expected ? "PASS" : "FAIL");

    // Test converting subnormal to integer
    int32_t int_result;
    __asm__ volatile("fcvt.w.s %0, %1" : "=r"(int_result) : "f"(subnormal1));
    expected = (int32_t)subnormal1;
    printf("fcvt.w.s (Subnormal): fcvt.w(%e) = %d, Expected: %d %s\n", subnormal1, int_result, (int32_t)expected, int_result == (int32_t)expected ? "PASS" : "FAIL");

    // Test converting subnormal to unsigned integer
    uint32_t uint_result;
    __asm__ volatile("fcvt.wu.s %0, %1" : "=r"(uint_result) : "f"(subnormal1));
    expected = (uint32_t)subnormal1;
    printf("fcvt.wu.s (Subnormal): fcvt.wu(%e) = %u, Expected: %u %s\n", subnormal1, uint_result, (uint32_t)expected, uint_result == (uint32_t)expected ? "PASS" : "FAIL");

    // Test converting integer to subnormal (should result in zero)
    int32_t int_input = 0;
    __asm__ volatile("fcvt.s.w %0, %1" : "=f"(result) : "r"(int_input));
    expected = (float)int_input;
    printf("fcvt.s.w (Subnormal): fcvt.s(%d) = %e, Expected: %e %s\n", int_input, result, expected, result == expected ? "PASS" : "FAIL");

    // Test converting unsigned integer to subnormal (should result in zero)
    uint32_t uint_input = 0;
    __asm__ volatile("fcvt.s.wu %0, %1" : "=f"(result) : "r"(uint_input));
    expected = (float)uint_input;
    printf("fcvt.s.wu (Subnormal): fcvt.s(%u) = %e, Expected: %e %s\n", uint_input, result, expected, result == expected ? "PASS" : "FAIL");
}

int main() {
    printf("Running test: subnormal_arithmetic\n");
    initialize_registers();
    test_subnormal_arithmetic();
    return 0;
}
