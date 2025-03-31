#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <hw_defines.h>


int main() {
  testcase_init();

  /* START TEST */
  enable_simple_multicore_printf(APU_CORE_5);

  start_core(PVE_0_CLUSTER_0_CORE_0);
  start_core(AI_CORE_0);
  CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(PVE_0_CLUSTER_0_CORE_0));
  CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(AI_CORE_0));

  disable_simple_multicore_printf(APU_CORE_5);

  /* END TEST */
  return testcase_finalize();
}

