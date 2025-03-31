#include "common.h"
#include "testutils.h"

// Function to set a floating-point value by its bit pattern
float set_float_by_bits(uint32_t bits) {
    float result;
    memcpy(&result, &bits, sizeof(result));
    return result;
}

// Function to test the single-precision floating-point classify instruction (fclass.s)
void test_single_prec_fp_classify_instr() {
    float values[] = {
        set_float_by_bits(0x00000000),  // Positive zero
        set_float_by_bits(0x80000000),  // Negative zero
        set_float_by_bits(0x3F800000),  // Normalized positive (1.0)
        set_float_by_bits(0xBF800000),  // Normalized negative (-1.0)
        set_float_by_bits(0x7F800000),  // Positive infinity
        set_float_by_bits(0xFF800000),  // Negative infinity
        set_float_by_bits(0x7FC00000),  // Quiet NaN
        set_float_by_bits(0x00000001),  // Subnormal positive (smallest positive subnormal)
        set_float_by_bits(0x80000001),  // Subnormal negative (smallest negative subnormal)
        set_float_by_bits(0x40490FDB),  // Normal positive value (π)
        set_float_by_bits(0xC0490FDB),  // Normal negative value (-π)
        set_float_by_bits(0x3EAAAAAB),  // Normalized positive (fraction 1/3)
        set_float_by_bits(0xBEAAAAAB),  // Normalized negative (fraction -1/3)
        1.0f / 0.0f,                    // Positive infinity from division
        -1.0f / 0.0f,                   // Negative infinity from division
        0.0f / 0.0f,                    // NaN from division by zero
        set_float_by_bits(0x00000001),  // Subnormal positive (1.0 * 1.0e-45)
        set_float_by_bits(0x80000001),  // Subnormal negative (-1.0 * 1.0e-45)
        (1.0f / 0.0f) - (1.0f / 0.0f)   // NaN resulting from infinity - infinity
    };

    const char* descriptions[] = {
        "Positive zero",
        "Negative zero",
        "Normalized positive",
        "Normalized negative",
        "Positive infinity",
        "Negative infinity",
        "Quiet NaN",
        "Subnormal positive",
        "Subnormal negative",
        "Pi (π)",
        "Negative Pi (-π)",
        "Normalized positive (fraction 1/3)",
        "Normalized negative (fraction -1/3)",
        "Positive infinity (1.0 / 0.0)",
        "Negative infinity (-1.0 / 0.0)",
        "NaN from 0.0 / 0.0",
        "Subnormal positive (1.0 * 1.0e-45)",
        "Subnormal negative (-1.0 * 1.0e-45)",
        "NaN from (inf - inf)"
    };

    // Initialize test counters
    testcase_init();

    int result;
    int num_tests = 19;  // Set the number of test cases explicitly

    // Run the tests
    for (int i = 0; i < num_tests; i++) {
        __asm__ volatile("fclass.s %0, %1" : "=r"(result) : "f"(values[i]));
        printf("\ncase: %d fclass.s: fclass(%s) = 0x%x\n", i, descriptions[i], result);

        // Corrected expected classifications
        int expected = 0;
        switch (i) {
            case 0: expected = 0x10; break; // Positive zero
            case 1: expected = 0x08; break; // Negative zero
            case 2: expected = 0x40; break; // Normalized positive
            case 3: expected = 0x02; break; // Normalized negative
            case 4: expected = 0x80; break; // Positive infinity
            case 5: expected = 0x01; break; // Negative infinity
            case 6: expected = 0x200; break; // Quiet NaN
            case 7: expected = 0x20; break; // Subnormal positive
            case 8: expected = 0x04; break; // Subnormal negative
            case 9: expected = 0x40; break; // Normal positive (π)
            case 10: expected = 0x02; break; // Normal negative (-π)
            case 11: expected = 0x40; break; // Normal positive (1/3)
            case 12: expected = 0x02; break; // Normal negative (-1/3)
            case 13: expected = 0x80; break; // Positive infinity (1.0 / 0.0)
            case 14: expected = 0x01; break; // Negative infinity (-1.0 / 0.0)
            case 15: expected = 0x200; break; // NaN from 0.0 / 0.0
            case 16: expected = 0x20; break; // Subnormal positive (1.0 * 1.0e-45)
            case 17: expected = 0x04; break; // Subnormal negative (-1.0 * 1.0e-45)
            case 18: expected = 0x200; break; // NaN from (inf - inf)
        }

        // Use CHECK_EQUAL_INT to verify the result against expected value
        CHECK_EQUAL_INT(expected, result, "fclass(%s) failed", descriptions[i]);
    }

    // Finalize the test and return the overall result
    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }
}

int main() {
    printf("Running test: single_prec_fp_classify_instr\n");
    initialize_registers();
    test_single_prec_fp_classify_instr();
    return testcase_finalize(); // Return final test result
}
