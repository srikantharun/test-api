#include <platform.h>
#include <testutils.h>
#include <timer.h>
#include <thread.h>
#include <multicore.h>
#include <hw_defines.h>

int main() {
  testcase_init();

  /* START TEST */
  printf("Starting RVV test:\n");
  printf("********************************\n");
  enable_simple_multicore_printf(APU_CORE_5);

  // Start all cores
  if (HW_DEFINES_AICORE_MODULE_NUMBER > 0) {
    start_core(AI_CORE_0);
  }
  for(uint32_t coreid = PVE_0_CLUSTER_0_CORE_0; coreid < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER; coreid+=2)
  {
    start_core(coreid);
  }
  for(uint32_t coreid = PVE_1_CLUSTER_0_CORE_0; coreid < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER; coreid+=2)
  {
    start_core(coreid);
  }

  // Wait for all cores to finish
  if (HW_DEFINES_AICORE_MODULE_NUMBER > 0) {
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(AI_CORE_0), "Failed to return properly on the AICORE.");
  }
  for(uint32_t coreid = PVE_0_CLUSTER_0_CORE_0; coreid < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER; coreid+=2)
  {
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(coreid), "Failed to return properly on the PVE0.");
  }
  for(uint32_t coreid = PVE_1_CLUSTER_0_CORE_0; coreid < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER; coreid+=2)
  {
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(coreid), "Failed to return properly on the PVE1.");
  }

  disable_simple_multicore_printf(APU_CORE_5);
  printf("********************************\n");

   /* END TEST */
  return testcase_finalize();
}
