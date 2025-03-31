// check that all RISC-Vs are able to reach all targets memories

#include "test_address_space_memory/address_space_utils.h"
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>
#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <printf.h>
#include <thread.h>

int main(void) {
  testcase_init();

  // enable modules
  // L2
  pctl_enable_l2();
  // PVE_0
  pctl_enable_pve_0();
  // AICOREs
  for (uint32_t i=AI_CORE_0; i < (AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER); i++){
    pctl_enable_aicore(i);
  }

  enable_simple_multicore_printf(APU_CORE_5);
  // run it for 1 pve_1_core since it takes approx 13min to run for each core.
  for (uint32_t pve_core = PVE_1_CLUSTER_0_CORE_0; pve_core < PVE_1_CLUSTER_0_CORE_1; pve_core++){
    start_core(pve_core);
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(pve_core));
  }
  disable_simple_multicore_printf(APU_CORE_5);

  return testcase_finalize();
}
