#include "common.h"

// Define the floating-point values for testing
float test_values[12];
float expected_results[12][6]; // Expected results for 6 rounding modes

// Rounding mode constants
#define ROUND_RNE 0 // Round to Nearest, ties to Even
#define ROUND_RTZ 1 // Round towards Zero
#define ROUND_RDN 2 // Round Downwards (towards -Infinity)
#define ROUND_RUP 3 // Round Upwards (towards +Infinity)
#define ROUND_RMM 4 // Round to Nearest, ties to Max Magnitude
#define ROUND_DYN 5 // Dynamic rounding mode

// Initialize test values and expected results
void initialize_rounding_mode_test_values() {
    test_values[0] = 1.4f;
    test_values[1] = 1.5f;
    test_values[2] = -1.5f;
    test_values[3] = 2.5f;
    test_values[4] = 0.4f;
    test_values[5] = -0.4f;
    test_values[6] = 123456.789f;
    test_values[7] = -123456.789f;
    test_values[8] = *((float*)&(uint32_t){POS_INFINITY});
    test_values[9] = *((float*)&(uint32_t){NEG_INFINITY});
    test_values[10] = *((float*)&(uint32_t){NAN_VALUE});
    test_values[11] = -1.0f;

    // Initialize expected results for each rounding mode
    expected_results[0][ROUND_RNE] = 1.0f;  expected_results[0][ROUND_RTZ] = 1.0f;  expected_results[0][ROUND_RDN] = 1.0f;  expected_results[0][ROUND_RUP] = 2.0f;  expected_results[0][ROUND_RMM] = 1.0f;  expected_results[0][ROUND_DYN] = 1.0f;
    expected_results[1][ROUND_RNE] = 2.0f;  expected_results[1][ROUND_RTZ] = 1.0f;  expected_results[1][ROUND_RDN] = 1.0f;  expected_results[1][ROUND_RUP] = 2.0f;  expected_results[1][ROUND_RMM] = 2.0f;  expected_results[1][ROUND_DYN] = 2.0f;
    expected_results[2][ROUND_RNE] = -2.0f; expected_results[2][ROUND_RTZ] = -1.0f; expected_results[2][ROUND_RDN] = -2.0f; expected_results[2][ROUND_RUP] = -1.0f; expected_results[2][ROUND_RMM] = -2.0f; expected_results[2][ROUND_DYN] = -2.0f;
    expected_results[3][ROUND_RNE] = 2.0f;  expected_results[3][ROUND_RTZ] = 2.0f;  expected_results[3][ROUND_RDN] = 2.0f;  expected_results[3][ROUND_RUP] = 3.0f;  expected_results[3][ROUND_RMM] = 2.0f;  expected_results[3][ROUND_DYN] = 2.0f;
    expected_results[4][ROUND_RNE] = 0.0f;  expected_results[4][ROUND_RTZ] = 0.0f;  expected_results[4][ROUND_RDN] = 0.0f;  expected_results[4][ROUND_RUP] = 1.0f;  expected_results[4][ROUND_RMM] = 0.0f;  expected_results[4][ROUND_DYN] = 0.0f;
    expected_results[5][ROUND_RNE] = 0.0f;  expected_results[5][ROUND_RTZ] = 0.0f;  expected_results[5][ROUND_RDN] = -1.0f; expected_results[5][ROUND_RUP] = 0.0f;  expected_results[5][ROUND_RMM] = 0.0f;  expected_results[5][ROUND_DYN] = 0.0f;
    expected_results[6][ROUND_RNE] = 123457.0f; expected_results[6][ROUND_RTZ] = 123456.0f; expected_results[6][ROUND_RDN] = 123456.0f; expected_results[6][ROUND_RUP] = 123457.0f; expected_results[6][ROUND_RMM] = 123457.0f; expected_results[6][ROUND_DYN] = 123457.0f;
    expected_results[7][ROUND_RNE] = -123457.0f; expected_results[7][ROUND_RTZ] = -123456.0f; expected_results[7][ROUND_RDN] = -123457.0f; expected_results[7][ROUND_RUP] = -123456.0f; expected_results[7][ROUND_RMM] = -123457.0f; expected_results[7][ROUND_DYN] = -123457.0f;
    expected_results[8][ROUND_RNE] = *((float*)&(uint32_t){POS_INFINITY}); expected_results[8][ROUND_RTZ] = *((float*)&(uint32_t){POS_INFINITY}); expected_results[8][ROUND_RDN] = *((float*)&(uint32_t){POS_INFINITY}); expected_results[8][ROUND_RUP] = *((float*)&(uint32_t){POS_INFINITY}); expected_results[8][ROUND_RMM] = *((float*)&(uint32_t){POS_INFINITY}); expected_results[8][ROUND_DYN] = *((float*)&(uint32_t){POS_INFINITY});
    expected_results[9][ROUND_RNE] = *((float*)&(uint32_t){NEG_INFINITY}); expected_results[9][ROUND_RTZ] = *((float*)&(uint32_t){NEG_INFINITY}); expected_results[9][ROUND_RDN] = *((float*)&(uint32_t){NEG_INFINITY}); expected_results[9][ROUND_RUP] = *((float*)&(uint32_t){NEG_INFINITY}); expected_results[9][ROUND_RMM] = *((float*)&(uint32_t){NEG_INFINITY}); expected_results[9][ROUND_DYN] = *((float*)&(uint32_t){NEG_INFINITY});
    expected_results[10][ROUND_RNE] = *((float*)&(uint32_t){NAN_VALUE}); expected_results[10][ROUND_RTZ] = *((float*)&(uint32_t){NAN_VALUE}); expected_results[10][ROUND_RDN] = *((float*)&(uint32_t){NAN_VALUE}); expected_results[10][ROUND_RUP] = *((float*)&(uint32_t){NAN_VALUE}); expected_results[10][ROUND_RMM] = *((float*)&(uint32_t){NAN_VALUE}); expected_results[10][ROUND_DYN] = *((float*)&(uint32_t){NAN_VALUE});
    expected_results[11][ROUND_RNE] = -1.0f; expected_results[11][ROUND_RTZ] = 0.0f; expected_results[11][ROUND_RDN] = -1.0f; expected_results[11][ROUND_RUP] = 0.0f; expected_results[11][ROUND_RMM] = -1.0f; expected_results[11][ROUND_DYN] = -1.0f;
}


// Macro to set rounding mode
#define SET_ROUNDING_MODE(mode) asm volatile ("csrw fcsr, %0" :: "r"(mode))

// Macro to check the rounding result and print the result
#define CHECK_ROUNDING_RESULT(op, dest, expected_idx, mode, scenario)        \
    do {                                                                     \
        float dest_val;                                                      \
        char dest_str[50], expected_str[50];                                 \
        asm volatile ("fsw " #dest ", %0" : "=m"(dest_val));                 \
        float_to_str(dest_val, dest_str, 6);                                 \
        float_to_str(expected_results[expected_idx][mode], expected_str, 6); \
        const char *result = (fabsf(dest_val - expected_results[expected_idx][mode]) <= FLOAT_TOLERANCE) ? "PASS" : "FAIL"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);              \
        if (strcmp(result, "FAIL") == 0) pass = 0;                           \
    } while (0)

// Macro to perform a floating-point addition and check result
#define TEST_ROUNDING_OP(dest, src, op, value_idx, mode, mode_name)       \
    do {                                                                  \
        SET_ROUNDING_MODE(mode);                                          \
        asm volatile ("flw " #src ", %0" :: "m"(test_values[value_idx])); \
        asm volatile (#op " " #dest ", " #src ", " #src);                 \
        CHECK_ROUNDING_RESULT(#op, dest, value_idx, mode, "Test rounding " mode_name); \
    } while (0)

int main() {
    int pass = 1; // Assume pass unless a test fails

    // Initialize test values and expected results
    initialize_rounding_mode_test_values();

    // Clear FCSR before tests
    asm volatile("csrw fcsr, zero"); // Clear FCSR register before starting tests

    // Print table header
    PRINT_HEADER();

    // Test scenarios for each rounding mode
    for (int i = 0; i < 12; ++i) {
        TEST_ROUNDING_OP(fa0, fa1, fadd.s, i, ROUND_RNE, "RNE");
        TEST_ROUNDING_OP(fa0, fa1, fadd.s, i, ROUND_RTZ, "RTZ");
        TEST_ROUNDING_OP(fa0, fa1, fadd.s, i, ROUND_RDN, "RDN");
        TEST_ROUNDING_OP(fa0, fa1, fadd.s, i, ROUND_RUP, "RUP");
        TEST_ROUNDING_OP(fa0, fa1, fadd.s, i, ROUND_RMM, "RMM");
        TEST_ROUNDING_OP(fa0, fa1, fadd.s, i, ROUND_DYN, "DYN");
    }

    if (pass) {
        printf("All rounding mode tests passed.\n");
    } else {
        printf("Some rounding mode tests failed.\n");
    }

    return 0;
}
