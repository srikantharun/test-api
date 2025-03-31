// This is a test file for half_prec_fp_conv_move_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test various half-precision floating-point conversion and move instructions
void test_half_prec_fp_conv_move_instr() {
    uint16_t ha = 0x3C00;  // Half-precision representation of 1.0
    uint16_t hb = 0x4000;  // Half-precision representation of 2.0
    uint16_t result_half, expected_half;
    float result_float, expected_float;
    double result_double, expected_double;
    int32_t result_int, expected_int;
    int64_t result_long, expected_long;

    // Test fcvt.h.s (single-precision float to half-precision conversion)
    __asm__ volatile("fcvt.h.s %0, %1" : "=f"(result_half) : "f"(1.0f));
    expected_half = 0x3C00;  // Half-precision 1.0
    printf("fcvt.h.s: fcvt.h(%f) = %hx, Expected: %hx %s\n", 1.0f, result_half, expected_half, result_half == expected_half ? "PASS" : "FAIL");

    // Test fcvt.h.d (double-precision float to half-precision conversion)
    __asm__ volatile("fcvt.h.d %0, %1" : "=f"(result_half) : "f"(2.0));
    expected_half = 0x4000;  // Half-precision 2.0
    printf("fcvt.h.d: fcvt.h(%f) = %hx, Expected: %hx %s\n", 2.0, result_half, expected_half, result_half == expected_half ? "PASS" : "FAIL");

    // Test fcvt.s.h (half-precision to single-precision float conversion)
    __asm__ volatile("fcvt.s.h %0, %1" : "=f"(result_float) : "f"(ha));
    expected_float = 1.0f;  // Single-precision 1.0
    printf("fcvt.s.h: fcvt.s(%hx) = %f, Expected: %f %s\n", ha, result_float, expected_float, result_float == expected_float ? "PASS" : "FAIL");

    // Test fcvt.d.h (half-precision to double-precision float conversion)
    __asm__ volatile("fcvt.d.h %0, %1" : "=f"(result_double) : "f"(hb));
    expected_double = 2.0;  // Double-precision 2.0
    printf("fcvt.d.h: fcvt.d(%hx) = %f, Expected: %f %s\n", hb, result_double, expected_double, result_double == expected_double ? "PASS" : "FAIL");

    // Test fmv.x.h (move half-precision to integer)
    __asm__ volatile("fmv.x.h %0, %1" : "=r"(result_int) : "f"(ha));
    expected_int = ha;
    printf("fmv.x.h: fmv.x(%hx) = %d, Expected: %d %s\n", ha, result_int, expected_int, result_int == expected_int ? "PASS" : "FAIL");

    // Test fmv.h.x (move integer to half-precision)
    __asm__ volatile("fmv.h.x %0, %1" : "=f"(result_half) : "r"(result_int));
    expected_half = ha;
    printf("fmv.h.x: fmv.h(%d) = %hx, Expected: %hx %s\n", result_int, result_half, expected_half, result_half == expected_half ? "PASS" : "FAIL");

    // Test fcvt.h.w (signed integer to half-precision conversion)
    __asm__ volatile("fcvt.h.w %0, %1" : "=f"(result_half) : "r"(2));
    expected_half = 0x4000;  // Half-precision 2.0
    printf("fcvt.h.w: fcvt.h(%d) = %hx, Expected: %hx %s\n", 2, result_half, expected_half, result_half == expected_half ? "PASS" : "FAIL");

    // Test fcvt.h.l (signed long to half-precision conversion)
    __asm__ volatile("fcvt.h.l %0, %1" : "=f"(result_half) : "r"((int64_t)2));
    expected_half = 0x4000;  // Half-precision 2.0
    printf("fcvt.h.l: fcvt.h(%lld) = %hx, Expected: %hx %s\n", (int64_t)2, result_half, expected_half, result_half == expected_half ? "PASS" : "FAIL");

    // Test fcvt.w.h (half-precision to signed integer conversion)
    __asm__ volatile("fcvt.w.h %0, %1" : "=r"(result_int) : "f"(ha));
    expected_int = 1;  // Integer 1
    printf("fcvt.w.h: fcvt.w(%hx) = %d, Expected: %d %s\n", ha, result_int, expected_int, result_int == expected_int ? "PASS" : "FAIL");

    // Test fcvt.l.h (half-precision to signed long conversion)
    __asm__ volatile("fcvt.l.h %0, %1" : "=r"(result_long) : "f"(hb));
    expected_long = 2;  // Long 2
    printf("fcvt.l.h: fcvt.l(%hx) = %lld, Expected: %lld %s\n", hb, result_long, expected_long, result_long == expected_long ? "PASS" : "FAIL");
}


int main() {
    printf("Running test: half_prec_fp_conv_move_instr\n");
    initialize_registers();
    test_half_prec_fp_conv_move_instr();
    return 0;
}
