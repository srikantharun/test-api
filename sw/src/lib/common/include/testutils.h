// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

/**
 * Module: testutils.h (helper functions for testing)
 * Description: Verification framework that implements initialization and finalization functions
 * Source: -
 */

#pragma once

#include <stdbool.h>
#include <platform.h>
#include <encoding.h>
#include <log.h>

/* How to use the test utils
 *
 * The actual test helpers are very simple. You can run arbitrary checks and it will register the
 * number of successful/failed checks internally. In the end you return the overall test result.
 *
 * Note: The counters are per core. If you run tests on sys ctrl and ai core,
 * make sure to return the test result from ai-core to sys-ctrl and check that
 * it is TEST_SUCCESS.
 *
 * For an example usage check 'test_dhrystone.c'.
 */

#define TEST_SUCCESS 0
#define TEST_FAILURE 1

/* reset internal test counters */
void testcase_init(void);

/* return overall result (TEST_SUCCESS or TEST_FAILURE) depending on whether any checks failed */
int testcase_finalize(void);

/* returns true if any checks failed */
bool testcase_checks_failed();

/* return 1 if any checks failed, 0 otherwise. Puts test stats into the pointer arguments */
bool testcase_get_stats(long* check_count, long* fail_count);

// FOR INTERNAL USE ONLY: use CHECK_* macros instead.
int __check_true(int condition);
int __check_rtol(float ref, float val, float rtol, float atol);


// This macro is designed to measure the execution time of a given code block in terms of CPU cycles.
// It is useful for performance testing and benchmarking small code segments.
#define MEASURE(TEST)                \
  ({                                 \
    unsigned long runtime;           \
    unsigned long start = rdcycle(); \
    TEST;                            \
    runtime = rdcycle() - start;     \
    runtime;                         \
  })


/* wrapper around check_true which allows to easily print more debug information */

// If you want more information on mismatches, define VERBOSE_TESTUTILS
#ifndef VERBOSE_TESTUTILS
#define VERBOSE_TESTUTILS
#endif

#ifdef VERBOSE_TESTUTILS
#include <printf.h>

// Check if condition it true and register success or failure internally.
#define CHECK_TRUE(condition, ...) (                                                                                      \
    __check_true((condition)) ? 1 : ({                                                                                    \
        LOG_WRN("[CHECK FAILED] %s:%d:%s: Expected 'true', Was 'false', " __VA_ARGS__, __FILE__, __LINE__, __FUNCTION__); \
    0;                                                                                                                    \
})                                                                                                                        \
)

// Check if hexadecimals equal and register success or failure internally.
#define CHECK_EQUAL_HEX(ref, val, ...) ({                                                                                          \
    int64_t _ref = (int64_t)(ref);                                                                                                 \
    int64_t _val = (int64_t)(val);                                                                                                 \
    __check_true(_ref == _val) ? 1 : ({                                                                                            \
        LOG_WRN("[CHECK FAILED] %s:%d:%s: Expected 0x%0x, Was 0x%0x, " __VA_ARGS__, __FILE__, __LINE__, __FUNCTION__, _ref, _val); \
        0;                                                                                                                         \
    });                                                                                                                            \
})

// Check if integers are equal and register success or failure internally.
#define CHECK_EQUAL_INT(ref, val, ...) ({                                                                                              \
    int64_t _ref = (int64_t)(ref);                                                                                                     \
    int64_t _val = (int64_t)(val);                                                                                                     \
    __check_true(_ref == _val) ? 1 : ({                                                                                                \
        LOG_WRN("[CHECK FAILED] %s:%d:%s: Expected \'%ld\', Was \'%ld\', " __VA_ARGS__, __FILE__, __LINE__, __FUNCTION__, _ref, _val); \
        0;                                                                                                                             \
    });                                                                                                                                \
})

// Check if floats are equal and register success or failure internally.
#define CHECK_EQUAL_FLOAT(ref, val, ...) ({                                                                                          \
    float _ref = (float)(ref);                                                                                                       \
    float _val = (float)(val);                                                                                                       \
    __check_true(_ref == _val) ? 1 : ({                                                                                              \
        LOG_WRN("[CHECK FAILED] %s:%d:%s: Expected \'%f\', Was \'%f\', " __VA_ARGS__, __FILE__, __LINE__, __FUNCTION__, _ref, _val); \
        0;                                                                                                                           \
    });                                                                                                                              \
})

// Check if characters are equal and register success or failure internally.
#define CHECK_EQUAL_CHAR(ref, val, ...) ({                                                                                           \
    char _ref = (char)(ref);                                                                                                         \
    char _val = (char)(val);                                                                                                         \
    __check_true(_ref == _val) ? 1 : ({                                                                                              \
        LOG_WRN("[CHECK FAILED] %s:%d:%s: Expected \'%c\', Was \'%c\', "__VA_ARGS__ , __FILE__, __LINE__, __FUNCTION__, _ref, _val); \
        0;                                                                                                                           \
    });                                                                                                                              \
})

/**
 * @brief Check if a given value patches a reference values with absolute and relative tolerances
 *
 * The check passes, if the following condition is met
 *
 * |ref – val| < rtol * |ref| + atol
 *
 * @param ref The reference to compare to
 * @param val The computed value which is to be compared
 * @param rtol Tolerance relative to the reference value `ref`
 * @param atol Tolerance absolute to the reference `ref`
 * @return int
 */
#define CHECK_RTOL(ref, val, rtol, atol, ...) ({                                                                                                   \
    float _ref = (float)(ref);                                                                                                                     \
    float _val = (float)(val);                                                                                                                     \
    float _rtol = (float)(rtol);                                                                                                                   \
    float _atol = (float)(atol);                                                                                                                   \
    __check_rtol(_ref, _val, _rtol, _atol) ? 1 : ({                                                                                                \
        LOG_WRN("[CHECK FAILED] %s:%d:%s: Expected \'%f\', Was \'%f\', With rtol+atol" __VA_ARGS__, __FILE__, __LINE__, __FUNCTION__, _ref, _val); \
        0;                                                                                                                                         \
    });                                                                                                                                            \
})

// Check if condition is true and immediately abort execution otherwise.
#define ASSERT(condition, ...) do {                                                           \
    if (!(condition)) {                                                                       \
        LOG_ERR("ASSERTION FAILED %s:%d:%s " __VA_ARGS__, __FILE__, __LINE__, __FUNCTION__);  \
        exit(TEST_FAILURE);                                                                   \
    }                                                                                         \
} while (0)

#else
#define CHECK_TRUE(condition, ...)   (__check_true(condition))
#define CHECK_EQUAL_INT(a, b, ...)   (__check_true((a) == (b)))
#define CHECK_EQUAL_FLOAT(a, b, ...) (__check_true((a) == (b)))
#define CHECK_EQUAL_CHAR(a, b, ...)  (__check_true((a) == (b)))
#define CHECK_RTOL(ref, valu, rtol, atol, ...) (__check_rtol((ref), (val), (rtol), (atol)))
#define ASSERT(condition, ...) (do {if (!(condition)) {exit(TEST_FAILURE);}} while (0))
#endif  // #ifdef VERBOSE_TESTUTILS


