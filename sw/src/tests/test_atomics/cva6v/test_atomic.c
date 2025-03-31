#include <testutils.h>
#include <test_atomics/atomic_helper.h>

int main() {
  testcase_init();

  /* START TEST */
  test_atomic_helper(NULL);

  /* END TEST */
  return testcase_finalize();
}
