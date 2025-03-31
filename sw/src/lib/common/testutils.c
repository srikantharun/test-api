// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <math.h>
#include <printf.h>
#include <stdbool.h>

#include "testutils.h"
#include "asm.h"

typedef struct {
  // Number of checks that were run
  long check_count;
  // Number of checks that failed
  long failure_count;
} testcase_t;

static __thread testcase_t testcase;

void testcase_init()
{
  testcase.check_count = 0;
  testcase.failure_count = 0;
}

int testcase_finalize()
{
  if (testcase.check_count == 0)
  {
    // We may have tests which don't use the check functions but still call
    // testcase_finalize(). As long as the return value is not used this should
    // not matter.
    LOG_WRN("[WARNING] The test did not do any check, but still called testcase_finalize(). Returning TEST_FAILURE!");
    return TEST_FAILURE;
  }
  if (testcase.failure_count)
  {
    LOG_ERR("[TEST FAILED] %ld out of %ld checks failed!", testcase.failure_count, testcase.check_count);
    return TEST_FAILURE;
  }
  LOG_INF("[TEST SUCCESSFUL] %ld checks passed", testcase.check_count);
  return TEST_SUCCESS;
}

int __check_true(int condition) {
  testcase.check_count++;
  if (!condition) testcase.failure_count++;
  return condition;
}

int __check_rtol(float ref, float val, float rtol, float atol) {
  return __check_true(fabsf(ref - val) < (rtol * fabsf(ref) + atol));
}

bool testcase_checks_failed() {
  return testcase.failure_count > 0;
}

bool testcase_get_stats(long* checks, long* fails) {
  *checks = testcase.check_count;
  *fails = testcase.failure_count;
  return testcase.failure_count > 0;
}

