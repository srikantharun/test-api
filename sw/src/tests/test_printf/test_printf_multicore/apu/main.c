#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <pctl_utils.h>
#include <regutils.h>


int main() {
  /* START TEST */
  testcase_init();
  printf("Hello from APU\n");
  enable_simple_multicore_printf(APU_CORE_5);

  // Start all cores
  start_cores_available();

  // Wait for all cores
  CHECK_EQUAL_INT(TEST_SUCCESS, wait_cores_available());

  disable_simple_multicore_printf(APU_CORE_5);

  printf("Bye from APU\n");

  /* END TEST */
  return testcase_finalize();
}
