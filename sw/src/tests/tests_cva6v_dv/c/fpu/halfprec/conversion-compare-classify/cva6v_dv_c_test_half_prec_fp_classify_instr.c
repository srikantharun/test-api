#include "common.h"
#include "testutils.h"

// Function to set a half-precision floating-point value by its bit pattern
uint16_t set_half_by_bits(uint16_t bits) {
    return bits;
}

// Function to test the half-precision floating-point classify instruction (fclass.h)
void test_half_prec_fp_classify_instr() {
    uint16_t values[] = {
        0x0000,  // Positive zero
        0x8000,  // Negative zero
        0x3C00,  // Normalized positive (1.0)
        0xBC00,  // Normalized negative (-1.0)
        0x7C00,  // Positive infinity
        0xFC00,  // Negative infinity
        0x7E00,  // Quiet NaN
        0x0400,  // Subnormal positive (smallest positive subnormal)
        0x8400,  // Subnormal negative (smallest negative subnormal)
        0x3555,  // Normal positive (approx. π/4)
        0xB555,  // Normal negative (approx. -π/4)
        0x3800,  // Normalized positive (fraction close to 1/3)
        0xB800,  // Normalized negative (fraction close to -1/3)
        0x7C00,  // Positive infinity (from division)
        0xFC00,  // Negative infinity (from division)
        0x7E00,  // Quiet NaN from division by zero
        0x03FF,  // Subnormal positive (smallest positive value)
        0x83FF,  // Subnormal negative (smallest negative value)
        0x7E00   // Quiet NaN from (inf - inf)
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
        "Normal positive (approx. π/4)",
        "Normal negative (approx. -π/4)",
        "Normalized positive (close to 1/3)",
        "Normalized negative (close to -1/3)",
        "Positive infinity (from division)",
        "Negative infinity (from division)",
        "Quiet NaN from division by zero",
        "Subnormal positive (smallest positive)",
        "Subnormal negative (smallest negative)",
        "Quiet NaN from (inf - inf)"
    };

    // Initialize test counters
    testcase_init();

    int result;
    int num_tests = 19;  // Set the number of test cases explicitly

    // Run the tests
    for (int i = 0; i < num_tests; i++) {
        uint16_t value = set_half_by_bits(values[i]); // Use the value directly as half-precision

        // Use inline assembly to move half-precision value into a floating-point register
        __asm__ volatile("fmv.h.x f0, %0" : : "r"(value)); // Move integer value to half float in f0
        __asm__ volatile("fclass.h %0, f0" : "=r"(result)); // Classify the half-precision number

        printf("\ncase: %d fclass.h: fclass(%s) = 0x%x\n", i, descriptions[i], result);

        // Expected classifications for each value
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
            case 9: expected = 0x40; break; // Normal positive (π/4)
            case 10: expected = 0x02; break; // Normal negative (-π/4)
            case 11: expected = 0x40; break; // Normal positive (1/3)
            case 12: expected = 0x02; break; // Normal negative (-1/3)
            case 13: expected = 0x80; break; // Positive infinity (from division)
            case 14: expected = 0x01; break; // Negative infinity (from division)
            case 15: expected = 0x200; break; // Quiet NaN from division by zero
            case 16: expected = 0x20; break; // Subnormal positive (smallest positive)
            case 17: expected = 0x04; break; // Subnormal negative (smallest negative)
            case 18: expected = 0x200; break; // Quiet NaN from (inf - inf)
        }

        // Use CHECK_EQUAL_INT to verify the result against expected value
        if (!CHECK_EQUAL_INT(expected, result, "fclass(%s) failed", descriptions[i])) {
            // Provide additional debug output
            printf("[DEBUG] Misclassification detected: value=0x%x, result=0x%x, expected=0x%x\n", value, result, expected);
        }
    }

    // Finalize the test and return the overall result
    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }
}

int main() {
    printf("Running test: half_prec_fp_classify_instr\n");
    initialize_registers();
    test_half_prec_fp_classify_instr();
    return testcase_finalize(); // Return final test result
}
