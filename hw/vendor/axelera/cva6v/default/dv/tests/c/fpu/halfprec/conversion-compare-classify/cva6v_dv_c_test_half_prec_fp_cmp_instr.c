// This is a test file for half_prec_fp_cmp_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test various half-precision floating-point comparison instructions
void test_half_prec_fp_cmp_instr() {
    uint16_t ha = 0x3C00;  // Half-precision representation of 1.0
    uint16_t hb = 0x4000;  // Half-precision representation of 2.0
    int result, expected;

    // Test feq.h (half-precision equality comparison)
    __asm__ volatile("feq.h %0, %1, %2" : "=r"(result) : "f"(ha), "f"(hb));
    expected = (ha == hb);
    printf("feq.h: feq(%hx, %hx) = %d, Expected: %d %s\n", ha, hb, result, expected, result == expected ? "PASS" : "FAIL");

    // Test flt.h (half-precision less-than comparison)
    __asm__ volatile("flt.h %0, %1, %2" : "=r"(result) : "f"(ha), "f"(hb));
    expected = (ha < hb);
    printf("flt.h: flt(%hx, %hx) = %d, Expected: %d %s\n", ha, hb, result, expected, result == expected ? "PASS" : "FAIL");

    // Test fle.h (half-precision less-than-or-equal comparison)
    __asm__ volatile("fle.h %0, %1, %2" : "=r"(result) : "f"(ha), "f"(hb));
    expected = (ha <= hb);
    printf("fle.h: fle(%hx, %hx) = %d, Expected: %d %s\n", ha, hb, result, expected, result == expected ? "PASS" : "FAIL");
}


int main() {
    printf("Running test: half_prec_fp_cmp_instr\n");
    initialize_registers();
    test_half_prec_fp_cmp_instr();
    return 0;
}
