// Test file for move and type-conversion floating-point operations
// CVA6V directed C tests: Author:  Abhilash Chadhar
// In this test file, the following floating-point operations are explicitly tested:
// fmv.x.w - Move single-precision floating-point to 32-bit integer
// fmv.w.x - Move 32-bit integer to single-precision floating-point
// fmv.s - Move single-precision floating-point value between registers

#include "common.h"

// Define arrays to store the test values
float float_values[13];  // Adjusted to allow extra edge cases like NaN and Infinity
int int_values[13];
float expected_float_values[13];
int expected_int_values[13];

// Function to initialize values for testing
void initialize_values() {
    // Initializing float values for fmv.x.w tests
    float_values[0] = 0.0f;              // 0x00000000
    float_values[1] = -0.0f;             // 0x80000000
    float_values[2] = 3.141592f;         // A common floating-point value (0x40490FDB)
    float_values[3] = -2.718281f;        // Another common floating-point value (0xC02DF854)
    float_values[4] = 1e-40f;            // Subnormal small positive (0x000116C2)
    float_values[5] = -1e-40f;           // Subnormal small negative (0x800116C2)
    float_values[6] = 8388608.0f;        // 2^23, exactly representable (0x4B000000)
    float_values[7] = -8388608.0f;       // -2^23 (0xCB000000)
    float_values[8] = 3.4028235e38f;     // Maximum finite float (0x7F7FFFFF)
    float_values[9] = -3.4028235e38f;    // Maximum finite negative float (0xFF7FFFFF)

    // Add additional cases for NaN, positive infinity, and negative infinity
    uint32_t nan_value = 0x7FC00000;
    uint32_t pos_inf_value = 0x7F800000;
    uint32_t neg_inf_value = 0xFF800000;

    memcpy(&float_values[10], &nan_value, sizeof(float));
    memcpy(&float_values[11], &pos_inf_value, sizeof(float));
    memcpy(&float_values[12], &neg_inf_value, sizeof(float));

    // Initializing integer values for fmv.w.x tests
    int_values[0] = 0x00000000;          // 0
    int_values[1] = 0x80000000;          // Negative zero representation
    int_values[2] = 0x40490FDB;          // 3.141592 in integer form
    int_values[3] = 0xC02DF854;          // -2.718281 in integer form
    int_values[4] = 0x000116C2;          // Small positive subnormal
    int_values[5] = 0x800116C2;          // Small negative subnormal
    int_values[6] = 0x4B000000;          // 2^23 in integer form
    int_values[7] = 0xCB000000;          // -2^23 in integer form
    int_values[8] = 0x7F7FFFFF;          // Maximum finite float in integer form
    int_values[9] = 0xFF7FFFFF;          // Maximum finite negative float in integer form

    // Expected results for fmv.x.w and fmv.w.x tests
    for (int i = 0; i < 10; i++) {
        expected_int_values[i] = int_values[i];         // The int representation should match
        expected_float_values[i] = float_values[i];     // The float representation should match
    }

    // Set expected values for NaN, Infinity cases
    expected_int_values[10] = 0;                        // NaN -> 0
    expected_int_values[11] = 2147483647;               // Positive infinity -> INT_MAX
    expected_int_values[12] = -2147483648;              // Negative infinity -> INT_MIN

    memcpy(&expected_float_values[10], &nan_value, sizeof(float));
    memcpy(&expected_float_values[11], &pos_inf_value, sizeof(float));
    memcpy(&expected_float_values[12], &neg_inf_value, sizeof(float));
}

// Modified CHECK_FMV_X_W macro to use CHECK_TRUE
#define CHECK_FMV_X_W(dest, src, idx, scenario)                                \
    do {                                                                       \
        int dest_val;                                                          \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("sw " #dest ", %0" : "=m"(dest_val));                    \
        int_to_str(dest_val, dest_str);                                        \
        int_to_str(expected_int_values[idx], expected_str);                    \
        const char* result = (dest_val != expected_int_values[idx]) ? "FAIL" : "PASS"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        CHECK_TRUE(dest_val == expected_int_values[idx],                       \
            "[CHECK FAILED] %s: Expected \'%s\', Was \'%s\'",                  \
            scenario, expected_str, dest_str);                                 \
    } while(0)

// Modified CHECK_FMV_W_X macro to use CHECK_TRUE
#define CHECK_FMV_W_X(dest, src, idx, scenario)                                \
    do {                                                                       \
        float dest_val;                                                        \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("fsw " #dest ", %0" : "=m"(dest_val));                   \
        float_to_str(dest_val, dest_str, 6);                                   \
        float_to_str(expected_float_values[idx], expected_str, 6);             \
        const char* result = (fabsf(dest_val - expected_float_values[idx]) > FLOAT_TOLERANCE) ? "FAIL" : "PASS"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        CHECK_TRUE(fabsf(dest_val - expected_float_values[idx]) <= FLOAT_TOLERANCE, \
            "[CHECK FAILED] %s: Expected \'%s\', Was \'%s\'",                  \
            scenario, expected_str, dest_str);                                 \
    } while(0)

// Modified CHECK_FMV_S macro to use CHECK_TRUE
#define CHECK_FMV_S(dest, src, idx, scenario)                                  \
    do {                                                                       \
        float dest_val;                                                        \
        char dest_str[50], expected_str[50];                                   \
        asm volatile ("fsw " #dest ", %0" : "=m"(dest_val));                   \
        float_to_str(dest_val, dest_str, 6);                                   \
        float_to_str(expected_float_values[idx], expected_str, 6);             \
        const char* result = (fabsf(dest_val - expected_float_values[idx]) > FLOAT_TOLERANCE) ? "FAIL" : "PASS"; \
        PRINT_RESULT(scenario, dest_str, expected_str, result);                \
        CHECK_TRUE(fabsf(dest_val - expected_float_values[idx]) <= FLOAT_TOLERANCE, \
            "[CHECK FAILED] %s: Expected \'%s\', Was \'%s\'",                  \
            scenario, expected_str, dest_str);                                 \
    } while(0)

// Macro to perform fmv.x.w test with scenario description
#define TEST_FMV_X_W(dest, src, idx, description)                              \
    do {                                                                       \
        asm volatile ("flw " #src ", %0" :: "m"(float_values[idx]));           \
        asm volatile ("fmv.x.w " #dest ", " #src);                             \
        CHECK_FMV_X_W(dest, src, idx, description);                            \
    } while(0)

// Macro to perform fmv.w.x test with scenario description
#define TEST_FMV_W_X(dest, src, idx, description)                              \
    do {                                                                       \
        asm volatile ("lw " #src ", %0" : : "m"(int_values[idx]));             \
        asm volatile ("fmv.w.x " #dest ", " #src);                             \
        CHECK_FMV_W_X(dest, src, idx, description);                            \
    } while(0)

// Macro to perform fmv.s test with scenario description
#define TEST_FMV_S(dest, src, idx, description)                                \
    do {                                                                       \
        asm volatile ("flw " #src ", %0" :: "m"(float_values[idx]));           \
        asm volatile ("fmv.s " #dest ", " #src);                               \
        CHECK_FMV_S(dest, src, idx, description);                              \
    } while(0)

int main() {
    testcase_init(); // Initialize test case counters

    // Initialize the floating-point and integer values
    initialize_values();

    // Set rounding mode "round to nearest"
    asm volatile("li t0, 0b00000000000000000000000000000000; csrw fcsr, t0"); // Set rounding mode

    // Print the table header
    PRINT_HEADER();

    // Testing fmv.x.w (move float to int)
    TEST_FMV_X_W(a0, fa0, 0, "Test moving 0.0f to integer");
    TEST_FMV_X_W(a0, fa0, 1, "Test moving -0.0f to integer");
    TEST_FMV_X_W(a0, fa0, 2, "Test moving 3.141592f to integer");
    TEST_FMV_X_W(a0, fa0, 3, "Test moving -2.718281f to integer");
    TEST_FMV_X_W(a0, fa0, 4, "Test moving small positive subnormal to integer");
    TEST_FMV_X_W(a0, fa0, 5, "Test moving small negative subnormal to integer");
    TEST_FMV_X_W(a0, fa0, 6, "Test moving 2^23 to integer");
    TEST_FMV_X_W(a0, fa0, 7, "Test moving -2^23 to integer");
    TEST_FMV_X_W(a0, fa0, 8, "Test moving max finite float to integer");
    TEST_FMV_X_W(a0, fa0, 9, "Test moving max finite negative float to integer");
    TEST_FMV_X_W(a0, fa0, 10, "Test moving NaN to integer (expected 0)");
    TEST_FMV_X_W(a0, fa0, 11, "Test moving +Infinity to integer (expected INT_MAX)");
    TEST_FMV_X_W(a0, fa0, 12, "Test moving -Infinity to integer (expected INT_MIN)");

    // Testing fmv.w.x (move int to float)
    TEST_FMV_W_X(fa0, a0, 0, "Test moving 0 to float");
    TEST_FMV_W_X(fa0, a0, 1, "Test moving negative zero to float");
    TEST_FMV_W_X(fa0, a0, 2, "Test moving 3.141592 as integer to float");
    TEST_FMV_W_X(fa0, a0, 3, "Test moving -2.718281 as integer to float");
    TEST_FMV_W_X(fa0, a0, 4, "Test moving small positive subnormal as integer to float");
    TEST_FMV_W_X(fa0, a0, 5, "Test moving small negative subnormal as integer to float");
    TEST_FMV_W_X(fa0, a0, 6, "Test moving 2^23 as integer to float");
    TEST_FMV_W_X(fa0, a0, 7, "Test moving -2^23 as integer to float");
    TEST_FMV_W_X(fa0, a0, 8, "Test moving max finite float as integer to float");
    TEST_FMV_W_X(fa0, a0, 9, "Test moving max finite negative float as integer to float");

    // Testing fmv.s (move float between registers)
    TEST_FMV_S(fa1, fa0, 0, "Move 0.0f between registers");
    TEST_FMV_S(fa1, fa0, 1, "Move -0.0f between registers");
    TEST_FMV_S(fa1, fa0, 2, "Move 3.141592f between registers");
    TEST_FMV_S(fa1, fa0, 3, "Move -2.718281f between registers");
    TEST_FMV_S(fa1, fa0, 4, "Move small positive subnormal between registers");
    TEST_FMV_S(fa1, fa0, 5, "Move small negative subnormal between registers");
    TEST_FMV_S(fa1, fa0, 6, "Move 2^23 between registers");
    TEST_FMV_S(fa1, fa0, 7, "Move -2^23 between registers");
    TEST_FMV_S(fa1, fa0, 8, "Move max finite float between registers");
    TEST_FMV_S(fa1, fa0, 9, "Move max finite negative float between registers");

    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }

    return 0;
}
