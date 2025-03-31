// This is a test file for nan_generation_propagation and other floating-point edge cases
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"
// Function to generate a NaN value
float generate_nan() {
    uint32_t nan_bits = 0x7FC00000;
    float nan_value;
    memcpy(&nan_value, &nan_bits, sizeof(nan_value));
    return nan_value;
}

// Function to generate a positive infinity value
float generate_pos_inf() {
    uint32_t inf_bits = 0x7F800000;
    float inf_value;
    memcpy(&inf_value, &inf_bits, sizeof(inf_value));
    return inf_value;
}

// Function to generate a negative infinity value
float generate_neg_inf() {
    uint32_t inf_bits = 0xFF800000;
    float inf_value;
    memcpy(&inf_value, &inf_bits, sizeof(inf_value));
    return inf_value;
}

// Function to test NaN and infinity propagation and other edge cases
void test_nan_infinity_propagation() {
    float nan = generate_nan(); // Generate a NaN value
    float pos_inf = generate_pos_inf(); // Generate positive infinity
    float neg_inf = generate_neg_inf(); // Generate negative infinity
    float zero = 0.0f;
    float one = 1.0f;
    float result;
    char hex_str_result[9];
    char hex_str_expected[9];

    // Test for NaN generation
    // Performing 0.0 / 0.0 should generate NaN
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(zero), "f"(zero));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("NaN Generation: 0.0 / 0.0 = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // Test for NaN propagation
    // NaN + 1.0 should propagate NaN
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(nan), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("NaN Propagation: NaN + 1.0 = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // NaN - 1.0 should propagate NaN
    __asm__ volatile("fsub.s %0, %1, %2" : "=f"(result) : "f"(nan), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("NaN Propagation: NaN - 1.0 = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // NaN * 1.0 should propagate NaN
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(nan), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("NaN Propagation: NaN * 1.0 = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // NaN / 1.0 should propagate NaN
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(nan), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("NaN Propagation: NaN / 1.0 = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // NaN sqrt should propagate NaN
    __asm__ volatile("fsqrt.s %0, %1" : "=f"(result) : "f"(nan));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("NaN Propagation: sqrt(NaN) = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // NaN min should return the non-NaN operand
    __asm__ volatile("fmin.s %0, %1, %2" : "=f"(result) : "f"(nan), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    int_to_hex(float_to_bits(one), hex_str_expected);
    printf("NaN Propagation: min(NaN, 1.0) = 0x%s (Expected: 0x%s) %s\n", hex_str_result, hex_str_expected, (result == one) ? "PASS" : "FAIL");

    // NaN max should return the non-NaN operand
    __asm__ volatile("fmax.s %0, %1, %2" : "=f"(result) : "f"(nan), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    int_to_hex(float_to_bits(one), hex_str_expected);
    printf("NaN Propagation: max(NaN, 1.0) = 0x%s (Expected: 0x%s) %s\n", hex_str_result, hex_str_expected, (result == one) ? "PASS" : "FAIL");

    // Positive infinity propagation
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(pos_inf), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    int_to_hex(float_to_bits(pos_inf), hex_str_expected);
    printf("Infinity Propagation: +Inf + 1.0 = 0x%s (Expected: 0x%s) %s\n", hex_str_result, hex_str_expected, (result == pos_inf) ? "PASS" : "FAIL");

    // Negative infinity propagation
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(neg_inf), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    int_to_hex(float_to_bits(neg_inf), hex_str_expected);
    printf("Infinity Propagation: -Inf + 1.0 = 0x%s (Expected: 0x%s) %s\n", hex_str_result, hex_str_expected, (result == neg_inf) ? "PASS" : "FAIL");

    // Positive infinity division
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(pos_inf), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    int_to_hex(float_to_bits(pos_inf), hex_str_expected);
    printf("Infinity Division: +Inf / 1.0 = 0x%s (Expected: 0x%s) %s\n", hex_str_result, hex_str_expected, (result == pos_inf) ? "PASS" : "FAIL");

    // Negative infinity division
    __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(result) : "f"(neg_inf), "f"(one));
    int_to_hex(float_to_bits(result), hex_str_result);
    int_to_hex(float_to_bits(neg_inf), hex_str_expected);
    printf("Infinity Division: -Inf / 1.0 = 0x%s (Expected: 0x%s) %s\n", hex_str_result, hex_str_expected, (result == neg_inf) ? "PASS" : "FAIL");

    // Infinity addition resulting in NaN
    __asm__ volatile("fadd.s %0, %1, %2" : "=f"(result) : "f"(pos_inf), "f"(neg_inf));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("Infinity Addition: +Inf + -Inf = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");

    // Infinity multiplication resulting in NaN
    __asm__ volatile("fmul.s %0, %1, %2" : "=f"(result) : "f"(pos_inf), "f"(zero));
    int_to_hex(float_to_bits(result), hex_str_result);
    printf("Infinity Multiplication: +Inf * 0.0 = 0x%s (Expected: NaN) %s\n", hex_str_result, isnan(result) ? "PASS" : "FAIL");
}


int main() {
    printf("Running test: nan_generation_propagation\n");
    initialize_registers();
    test_nan_infinity_propagation();
    return 0;
}
