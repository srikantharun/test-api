// This is a test file for fp_control_status_register
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test floating-point control and status register operations
void test_fp_control_status_register() {
    uint32_t fcsr;     // Floating-Point Control and Status Register
    uint32_t frm;      // Floating-Point Rounding Mode
    uint32_t fflags;   // Floating-Point Exception Flags
    float a = 3.5f, b = 2.5f, c = 0.0f, d = -1.0f, e = 1e30f, f = 1e-30f;
    char hex_str[9];   // Buffer to hold the hexadecimal string

    // Set the floating-point control and status register (fcsr)
    // Initialize fcsr to a known value
    __asm__ volatile("li %0, 0x0F" : "=r"(fcsr));
    __asm__ volatile("csrw fcsr, %0" :: "r"(fcsr));

    // Read the floating-point control and status register to verify
    __asm__ volatile("csrr %0, fcsr" : "=r"(fcsr));
    int_to_hex(fcsr, hex_str);
    printf("Initial fcsr value: 0x%s\n", hex_str);

    // Set the floating-point rounding mode (frm)
    // Initialize frm to round-to-nearest-even mode (RNE)
    __asm__ volatile("li %0, 0x0" : "=r"(frm));
    __asm__ volatile("csrw frm, %0" :: "r"(frm));

    // Read the floating-point rounding mode to verify
    __asm__ volatile("csrr %0, frm" : "=r"(frm));
    int_to_hex(frm, hex_str);
    printf("Initial frm value: 0x%s\n", hex_str);

    // Set the floating-point exception flags (fflags)
    // Initialize fflags to a known value
    __asm__ volatile("li %0, 0x1F" : "=r"(fflags));
    __asm__ volatile("csrw fflags, %0" :: "r"(fflags));

    // Read the floating-point exception flags to verify
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(fflags, hex_str);
    printf("Initial fflags value: 0x%s\n", hex_str);

    // Perform various floating-point operations to generate exceptions

    // Addition
    float result;
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    // Subtraction
    __asm__ volatile("fsub.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    // Multiplication
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(b));
    // Division by zero
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(a), "f"(c));
    // Square root of negative number
    __asm__ volatile("fsqrt.s %0, %1" : "=f"(result) : "f"(d));
    // Overflow
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(e), "f"(e));
    // Underflow
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(f), "f"(f));

    // Read and print the updated fcsr, frm, and fflags after the operations
    __asm__ volatile("csrr %0, fcsr" : "=r"(fcsr));
    int_to_hex(fcsr, hex_str);
    printf("Updated fcsr value: 0x%s\n", hex_str);

    __asm__ volatile("csrr %0, frm" : "=r"(frm));
    int_to_hex(frm, hex_str);
    printf("Updated frm value: 0x%s\n", hex_str);

    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(fflags, hex_str);
    printf("Updated fflags value: 0x%s\n", hex_str);

    // Check for various exceptions
    if (fflags & 0x01) printf("Invalid operation exception detected\n");
    if (fflags & 0x02) printf("Division by zero exception detected\n");
    if (fflags & 0x04) printf("Overflow exception detected\n");
    if (fflags & 0x08) printf("Underflow exception detected\n");
    if (fflags & 0x10) printf("Inexact exception detected\n");

    // Clear the floating-point exception flags
    __asm__ volatile("csrw fflags, %0" :: "r"(0));
    __asm__ volatile("csrr %0, fflags" : "=r"(fflags));
    int_to_hex(fflags, hex_str);
    printf("Cleared fflags value: 0x%s\n", hex_str);
}

int main() {
    printf("Running test: fp_control_status_register\n");
    initialize_registers();
    test_fp_control_status_register();
    return 0;
}
