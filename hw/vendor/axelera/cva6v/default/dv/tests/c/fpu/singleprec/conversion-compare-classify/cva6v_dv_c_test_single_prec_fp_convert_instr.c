// This is a test file for cva6v_dv_c_test_single_prec_fp_convert_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
// In this test file, the following floating-point operations are explicitly tested:
// fcvt.w.s - Convert floating-point single-precision to signed 32-bit integer
// fcvt.wu.s - Convert floating-point single-precision to unsigned 32-bit integer
// fcvt.s.w - Convert signed 32-bit integer to floating-point single-precision
// fcvt.s.wu - Convert unsigned 32-bit integer to floating-point single-precision

#include "common.h"

// Declare the floating-point values array
float float_values[25]; // Expanded array to accommodate more cases
int expected_int_values[25];    // Store expected integer values for comparisons
unsigned int expected_uint_values[25]; // Store expected unsigned integer values for comparisons
float expected_float_values[25]; // Store expected floating-point values for comparisons

// Function to initialize floating-point values and expected results
void initialize_values() {
    float_values[0] = 0.0f;               // 0x00000000 Zero
    float_values[1] = -0.0f;              // 0x80000000 Negative Zero
    float_values[2] = 1.0f;               // 0x3F800000 Normal positive
    float_values[3] = -1.0f;              // 0xBF800000 Normal negative
    float_values[4] = 1.5f;               // 0x3FC00000 Positive fractional
    float_values[5] = -1.5f;              // 0xBFC00000 Negative fractional
    float_values[6] = 1000.0f;            // 0x447A0000 Large positive
    float_values[7] = -1000.0f;           // 0xC47A0000 Large negative
    float_values[8] = 32767.0f;           // 0x46FFFE00 Maximum positive for 32-bit signed
    float_values[9] = -32768.0f;          // 0xC7000000 Maximum negative for 32-bit signed
    float_values[10] = 4.2e9f;            // 0x4E9F5C28 Exceeds 32-bit unsigned range
    float_values[11] = -4.2e9f;           // 0xCE9F5C28 Exceeds 32-bit signed range

    // Special values: Infinity, Negative Infinity, NaN
    memcpy(&float_values[12], &(float){0x7F800000}, sizeof(float)); // Positive Infinity
    memcpy(&float_values[13], &(float){0xFF800000}, sizeof(float)); // Negative Infinity
    memcpy(&float_values[14], &(float){0x7FC00000}, sizeof(float)); // NaN

    // Additional edge cases
    float_values[15] = 1.9999999f;        // Just below 2, rounding test
    float_values[16] = 2.0000001f;        // Just above 2, rounding test
    float_values[17] = 0.4999999f;        // Just below 0.5
    float_values[18] = 0.5f;              // Exactly 0.5
    float_values[19] = 0.5000001f;        // Just above 0.5
    float_values[20] = 1e-40f;            // Subnormal small positive
    float_values[21] = -1e-40f;           // Subnormal small negative
    float_values[22] = 3.4028235e38f;     // Maximum positive finite float (just below +Inf)
    float_values[23] = -3.4028235e38f;    // Maximum negative finite float (just above -Inf)
    float_values[24] = 8388608.0f;        // 2^23, exactly representable in IEEE-754

    // Expected integer conversions (for fcvt.w.s and fcvt.wu.s)
    expected_int_values[0] = 0;            // 0.0f -> 0
    expected_int_values[1] = 0;            // -0.0f -> 0
    expected_int_values[2] = 1;            // 1.0f -> 1
    expected_int_values[3] = -1;           // -1.0f -> -1
    expected_int_values[4] = 2;            // 1.5f -> 1 (enears)
    expected_int_values[5] = -2;           // -1.5f -> -1 (nearest)
    expected_int_values[6] = 1000;         // 1000.0f -> 1000
    expected_int_values[7] = -1000;        // -1000.0f -> -1000
    expected_int_values[8] = 32767;        // 32767.0f -> 32767
    expected_int_values[9] = -32768;       // -32768.0f -> -32768
    expected_int_values[10] = 2147483647;  // 4.2e9f -> saturates to INT_MAX (overflow)
    expected_int_values[11] = -2147483648; // -4.2e9f -> saturates to INT_MIN (overflow)
    expected_int_values[12] = 2139095040;  // Positive Infinity -> saturates to FLT_MAX
    expected_int_values[13] = 2147483647; // Negative Infinity -> saturates to INT_MIN
    expected_int_values[14] = 2143289344;  // NaN -> 2143289344 (Spike output)
    expected_int_values[15] = 2;           // 1.9999999f -> truncate to 1
    expected_int_values[16] = 2;           // 2.0000001f -> truncate to 2
    expected_int_values[17] = 0;           // 0.4999999f -> truncate to 0
    expected_int_values[18] = 0;           // 0.5f -> truncate to 0
    expected_int_values[19] = 1;           // 0.5000001f -> truncate to 0
    expected_int_values[20] = 0;           // 1e-40f -> truncate to 0 (subnormal)
    expected_int_values[21] = 0;           // -1e-40f -> truncate to 0 (subnormal)
    expected_int_values[22] = 2147483647;  // Max positive finite -> saturates to INT_MAX
    expected_int_values[23] = -2147483648; // Max negative finite -> saturates to INT_MIN
    expected_int_values[24] = 8388608;     // 2^23 -> exactly 8388608

    // Expected unsigned integer conversions (for fcvt.wu.s)
    expected_uint_values[0] = 0U;          // 0.0f -> 0U
    expected_uint_values[1] = 0U;          // -0.0f -> 0U
    expected_uint_values[2] = 1U;          // 1.0f -> 1U
    expected_uint_values[3] = 0U;          // -1.0f -> saturates to 0U (negative to unsigned)
    expected_uint_values[4] = 2U;          // 1.5f -> 1U (truncate)
    expected_uint_values[5] = 0U;          // -1.5f -> saturates to 0U
    expected_uint_values[6] = 1000U;       // 1000.0f -> 1000U
    expected_uint_values[7] = 0U;          // -1000.0f -> saturates to 0U
    expected_uint_values[8] = 32767U;      // 32767.0f -> 32767U
    expected_uint_values[9] = 0U;          // -32768.0f -> saturates to 0U
    expected_uint_values[10] = 4294967295U; // 4.2e9f -> saturates to UINT_MAX (overflow)
    expected_uint_values[11] = 0U;         // -4.2e9f -> saturates to 0U
    expected_uint_values[12] = 4294967295U; // Positive Infinity -> saturates to UINT_MAX
    expected_uint_values[13] = 0U;         // Negative Infinity -> saturates to 0U
    expected_uint_values[14] = 0U;         // NaN -> treated as 0U
    expected_uint_values[15] = 2U;         // 1.9999999f -> truncate to 1U
    expected_uint_values[16] = 2U;         // 2.0000001f -> truncate to 2U
    expected_uint_values[17] = 0U;         // 0.4999999f -> truncate to 0U
    expected_uint_values[18] = 0U;         // 0.5f -> truncate to 0U
    expected_uint_values[19] = 1U;         // 0.5000001f -> truncate to 0U
    expected_uint_values[20] = 0U;         // 1e-40f -> truncate to 0U (subnormal)
    expected_uint_values[21] = 0U;         // -1e-40f -> truncate to 0U (subnormal)
    expected_uint_values[22] = 4294967295U; // Max positive finite -> saturates to UINT_MAX
    expected_uint_values[23] = 0U;         // Max negative finite -> saturates to 0U
    expected_uint_values[24] = 8388608U;   // 2^23 -> exactly 8388608U

    // Expected float conversions (for fcvt.s.w and fcvt.s.wu)
    expected_float_values[0] = 0.0f;       // 0 -> 0.0f
    expected_float_values[1] = 1.0f;       // 1 -> 1.0f
    expected_float_values[2] = -1.0f;      // -1 -> -1.0f
    expected_float_values[3] = 1000.0f;    // 1000 -> 1000.0f
    expected_float_values[4] = -1000.0f;   // -1000 -> -1000.0f
    expected_float_values[5] = 32767.0f;   // 32767 -> 32767.0f
    expected_float_values[6] = -32768.0f;  // -32768 -> -32768.0f
    expected_float_values[7] = 4294967295.0f; // UINT_MAX -> 4294967295.0f
    expected_float_values[8] = 8388608.0f;    // 2^23 -> 8388608.0f
}

// Macro to check integer conversion result
#define CHECK_IREG(op, dest, expected_idx, signed_check, scenario)             \
    do {                                                                       \
        int dest_val;                                                          \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("sw " #dest ", %0" : "=m"(dest_val));                    \
        int_to_str(dest_val, dest_str);                                        \
        int_to_str(signed_check ? expected_int_values[expected_idx] : (int)expected_uint_values[expected_idx], expected_str); \
        const char *result = (dest_val == (signed_check ? expected_int_values[expected_idx] : (int)expected_uint_values[expected_idx])) ? "PASS" : "FAIL"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        CHECK_TRUE((dest_val == (signed_check ? expected_int_values[expected_idx] : (int)expected_uint_values[expected_idx])) , \
            "[CHECK FAILED] %s: Expected \'%s\', Was \'%s\'", scenario, expected_str, dest_str); \
    } while(0)

// Macro to perform floating-point to integer conversion and check result with scenario description
#define TEST_FCVT_TO_INT(dest, src, op, src_idx, expected_idx, signed_check, description) \
    do {                                                                                 \
        asm volatile ("flw " #src ", %0" :: "m"(float_values[src_idx]));                 \
        asm volatile (#op " " #dest ", " #src);                                          \
        CHECK_IREG(#op, dest, expected_idx, signed_check, description);                  \
    } while(0)

// Macro to check float conversion result
#define CHECK_FREG_FCVT(op, dest, expected_idx, scenario)                                \
    do {                                                                       \
        float dest_val;                                                        \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("fsw " #dest ", %0" : "=m"(dest_val));                   \
        float_to_str(dest_val, dest_str, 6);                                   \
        float_to_str(expected_float_values[expected_idx], expected_str, 6);    \
        const char *result = (fabsf(dest_val - expected_float_values[expected_idx]) <= FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        CHECK_TRUE(fabsf(dest_val - expected_float_values[expected_idx]) <= FLOAT_TOLERANCE, \
            "[CHECK FAILED] %s: Expected \'%s\', Was \'%s\'", scenario, expected_str, dest_str); \
    } while(0)

// Macro to perform integer to floating-point conversion and check result with scenario description
#define TEST_FCVT_TO_FLOAT(dest, src, op, src_val, expected_idx, description)            \
    do {                                                                                 \
        asm volatile ("li " #src ", %0" : : "i"(src_val));                               \
        asm volatile (#op " " #dest ", " #src);                                          \
        CHECK_FREG_FCVT(#op, dest, expected_idx, description);                           \
    } while(0)

int main() {
    testcase_init(); // Initialize test case counters

    // Initialize the floating-point and integer values
    initialize_values();

    // Print table header
    PRINT_HEADER();

    //Rounding to the nearest
    asm volatile("csrr t0, fcsr; li t1, ~(0b111 << 5); and t0, t0, t1; li t1, 0b000 << 5; or t0, t0, t1; csrw fcsr, t0");

    // Testing fcvt.w.s (float to signed int)
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 0, 0, 1, "Convert 0.0f to 0");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 1, 1, 1, "Convert -0.0f to 0");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 2, 2, 1, "Convert 1.0f to 1");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 3, 3, 1, "Convert -1.0f to -1");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 4, 4, 1, "Convert 1.5f to 1 (truncate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 5, 5, 1, "Convert -1.5f to -1 (truncate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 6, 6, 1, "Convert 1000.0f to 1000");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 7, 7, 1, "Convert -1000.0f to -1000");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 8, 8, 1, "Convert 32767.0f to 32767");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 9, 9, 1, "Convert -32768.0f to -32768");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 10, 10, 1, "Convert 4.2e9f to INT_MAX (overflow)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 11, 11, 1, "Convert -4.2e9f to INT_MIN (overflow)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 12, 12, 1, "Convert +Infinity to INT_MAX");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 13, 13, 1, "Convert -Infinity to INT_MIN");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 14, 14, 1, "Convert NaN to 0");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 15, 15, 1, "Convert 1.9999999f to 1");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 16, 16, 1, "Convert 2.0000001f to 2");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 17, 17, 1, "Convert 0.4999999f to 0");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 18, 18, 1, "Convert 0.5f to 0");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 19, 19, 1, "Convert 0.5000001f to 0");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 20, 20, 1, "Convert 1e-40f to 0 (subnormal)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 21, 21, 1, "Convert -1e-40f to 0 (subnormal)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 22, 22, 1, "Convert max finite positive to INT_MAX");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.w.s, 23, 23, 1, "Convert max finite negative to INT_MIN");

    // Testing fcvt.wu.s (float to unsigned int)
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 0, 0, 0, "Convert 0.0f to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 1, 1, 0, "Convert -0.0f to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 2, 2, 0, "Convert 1.0f to 1U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 3, 3, 0, "Convert -1.0f to 0U (saturate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 4, 4, 0, "Convert 1.5f to 1U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 5, 5, 0, "Convert -1.5f to 0U (saturate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 6, 6, 0, "Convert 1000.0f to 1000U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 7, 7, 0, "Convert -1000.0f to 0U (saturate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 8, 8, 0, "Convert 32767.0f to 32767U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 9, 9, 0, "Convert -32768.0f to 0U (saturate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 10, 10, 0, "Convert 4.2e9f to UINT_MAX (overflow)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 11, 11, 0, "Convert -4.2e9f to 0U (saturate)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 12, 12, 0, "Convert +Infinity to UINT_MAX");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 13, 13, 0, "Convert -Infinity to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 14, 14, 0, "Convert NaN to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 15, 15, 0, "Convert 1.9999999f to 1U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 16, 16, 0, "Convert 2.0000001f to 2U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 17, 17, 0, "Convert 0.4999999f to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 18, 18, 0, "Convert 0.5f to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 19, 19, 0, "Convert 0.5000001f to 0U");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 20, 20, 0, "Convert 1e-40f to 0U (subnormal)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 21, 21, 0, "Convert -1e-40f to 0U (subnormal)");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 22, 22, 0, "Convert max finite positive to UINT_MAX");
    TEST_FCVT_TO_INT(a0, fa0, fcvt.wu.s, 23, 23, 0, "Convert max finite negative to 0U");

    // Testing fcvt.s.w (signed int to float)
    TEST_FCVT_TO_FLOAT(fa0, a0, fcvt.s.w, 32767, 5, "Convert 32767 to 32767.0f");
    TEST_FCVT_TO_FLOAT(fa0, a0, fcvt.s.w, -1000, 4, "Convert -1000 to -1000.0f");
    TEST_FCVT_TO_FLOAT(fa0, a0, fcvt.s.w, 8388608, 8, "Convert 2^23 to 8388608.0f");

    // Testing fcvt.s.wu (unsigned int to float)
    TEST_FCVT_TO_FLOAT(fa0, a0, fcvt.s.wu, 4294967295U, 7, "Convert UINT_MAX to 4294967295.0f");
    TEST_FCVT_TO_FLOAT(fa0, a0, fcvt.s.wu, 1U, 1, "Convert 1 to 1.0f");
    TEST_FCVT_TO_FLOAT(fa0, a0, fcvt.s.wu, 8388608U, 8, "Convert 2^23 to 8388608.0f");

    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }

    return 0;
}
