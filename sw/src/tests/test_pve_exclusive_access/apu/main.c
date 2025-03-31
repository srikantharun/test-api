#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <hw_defines.h>


int main() {
  testcase_init();

  /* START TEST */
  printf("*** PVE exclusive access test!\n");

  enable_simple_multicore_printf(APU_CORE_5);

  start_cores_pve0();
  if(HW_DEFINES_PVE_1_CORE_NUMBER) {
    start_cores_pve1();
  }

  CHECK_TRUE(wait_cores_pve0() == TEST_SUCCESS);
  if(HW_DEFINES_PVE_1_CORE_NUMBER) {
    CHECK_TRUE(wait_cores_pve1() == TEST_SUCCESS);
  }

  disable_simple_multicore_printf(APU_CORE_5);

  /* END TEST */
  return testcase_finalize();
}

