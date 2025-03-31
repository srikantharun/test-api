#include "common.h"
#include <stdint.h>

// Define a 128-bit integer type using a structure
typedef struct {
    uint64_t low;
    uint64_t high;
} uint128_t;

// Function to multiply two 64-bit integers and return a 128-bit result
uint128_t mul128(uint64_t a, uint64_t b) {
    uint128_t result;
    __asm__ (
        "mul %0, %2, %3\n"
        "mulh %1, %2, %3\n"
        : "=&r"(result.low), "=&r"(result.high)
        : "r"(a), "r"(b)
    );
    return result;
}

// Function to perform multiplication and division operations and verify the results
void test_int_mult_div_ops() {
    for (int i = 0; i < 10; i++) {  // Run 10 tests with random inputs
        int64_t a = rand() % 100000 - 50000;  // Random int64_t between -50000 and 49999
        int64_t b = rand() % 100000 - 50000;  // Random int64_t between -50000 and 49999
        int64_t result, expected;

        // Test multiplication (MUL)
        __asm__ volatile ("mul %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        expected = a * b;
        printf("MUL: %lld * %lld = %lld, Expected: %lld %s\n", a, b, result, expected, result == expected ? "PASS" : "FAIL");

        // Test multiplication high signed (MULH)
        uint128_t mulh_result = mul128((uint64_t)a, (uint64_t)b);
        expected = (int64_t)mulh_result.high;
        __asm__ volatile ("mulh %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        printf("MULH: %lld * %lld = %lld, Expected: %lld %s\n", a, b, result, expected, result == expected ? "PASS" : "FAIL");

        // Test multiplication high unsigned (MULHU)
        uint128_t mulhu_result = mul128((uint64_t)a, (uint64_t)b);
        expected = (int64_t)mulhu_result.high;
        __asm__ volatile ("mulhu %0, %1, %2" : "=r"(result) : "r"((uint64_t)a), "r"((uint64_t)b));
        printf("MULHU: %llu * %llu = %llu, Expected: %llu %s\n", (uint64_t)a, (uint64_t)b, (uint64_t)result, (uint64_t)expected, result == expected ? "PASS" : "FAIL");

        // Test multiplication high signed-unsigned (MULHSU)
        uint128_t mulhsu_result = mul128((uint64_t)a, (uint64_t)b);
        expected = (int64_t)mulhsu_result.high;
        __asm__ volatile ("mulhsu %0, %1, %2" : "=r"(result) : "r"(a), "r"((uint64_t)b));
        printf("MULHSU: %lld * %llu = %lld, Expected: %lld %s\n", a, (uint64_t)b, result, expected, result == expected ? "PASS" : "FAIL");

        // Test division signed (DIV)
        __asm__ volatile ("div %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        expected = a / b;
        printf("DIV: %lld / %lld = %lld, Expected: %lld %s\n", a, b, result, expected, result == expected ? "PASS" : "FAIL");

        // Test division unsigned (DIVU)
        __asm__ volatile ("divu %0, %1, %2" : "=r"(result) : "r"((uint64_t)a), "r"((uint64_t)b));
        expected = (uint64_t)a / (uint64_t)b;
        printf("DIVU: %llu / %llu = %llu, Expected: %llu %s\n", (uint64_t)a, (uint64_t)b, (uint64_t)result, (uint64_t)expected, result == expected ? "PASS" : "FAIL");

        // Test remainder signed (REM)
        __asm__ volatile ("rem %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        expected = a % b;
        printf("REM: %lld %% %lld = %lld, Expected: %lld %s\n", a, b, result, expected, result == expected ? "PASS" : "FAIL");

        // Test remainder unsigned (REMU)
        __asm__ volatile ("remu %0, %1, %2" : "=r"(result) : "r"((uint64_t)a), "r"((uint64_t)b));
        expected = (uint64_t)a % (uint64_t)b;
        printf("REMU: %llu %% %llu = %llu, Expected: %llu %s\n", (uint64_t)a, (uint64_t)b, (uint64_t)result, (uint64_t)expected, result == expected ? "PASS" : "FAIL");

        // Test multiplication word (MULW)
        __asm__ volatile ("mulw %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        expected = (int32_t)a * (int32_t)b;
        printf("MULW: %d * %d = %d, Expected: %d %s\n", (int32_t)a, (int32_t)b, (int32_t)result, (int32_t)expected, (int32_t)result == (int32_t)expected ? "PASS" : "FAIL");

        // Test division word signed (DIVW)
        __asm__ volatile ("divw %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        expected = (int32_t)a / (int32_t)b;
        printf("DIVW: %d / %d = %d, Expected: %d %s\n", (int32_t)a, (int32_t)b, (int32_t)result, (int32_t)expected, (int32_t)result == (int32_t)expected ? "PASS" : "FAIL");

        // Test division word unsigned (DIVUW)
        __asm__ volatile ("divuw %0, %1, %2" : "=r"(result) : "r"((uint32_t)a), "r"((uint32_t)b));
        expected = (uint32_t)a / (uint32_t)b;
        printf("DIVUW: %u / %u = %u, Expected: %u %s\n", (uint32_t)a, (uint32_t)b, (uint32_t)result, (uint32_t)expected, (uint32_t)result == (uint32_t)expected ? "PASS" : "FAIL");

        // Test remainder word signed (REMW)
        __asm__ volatile ("remw %0, %1, %2" : "=r"(result) : "r"(a), "r"(b));
        expected = (int32_t)a % (int32_t)b;
        printf("REMW: %d %% %d = %d, Expected: %d %s\n", (int32_t)a, (int32_t)b, (int32_t)result, (int32_t)expected, (int32_t)result == (int32_t)expected ? "PASS" : "FAIL");

        // Test remainder word unsigned (REMUW)
        __asm__ volatile ("remuw %0, %1, %2" : "=r"(result) : "r"((uint32_t)a), "r"((uint32_t)b));
        expected = (uint32_t)a % (uint32_t)b;
        printf("REMUW: %u %% %u = %u, Expected: %u %s\n", (uint32_t)a, (uint32_t)b, (uint32_t)result, (uint32_t)expected, (uint32_t)result == (uint32_t)expected ? "PASS" : "FAIL");
    }
}

int main() {
    printf("Running test: int_mult_div_ops\n");
    initialize_registers();
    test_int_mult_div_ops();
    return 0;
}
