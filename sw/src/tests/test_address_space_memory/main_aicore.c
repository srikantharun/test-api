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
  // PVE_1
  pctl_enable_pve_1();
  // AICOREs
  for (uint32_t i=AI_CORE_0; i < (AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER); i++){
    pctl_enable_aicore(i);
  }

  enable_simple_multicore_printf(APU_CORE_5);
  for (uint32_t aicore_id = AI_CORE_0; aicore_id <= AI_CORE_7; aicore_id++){
    start_core(aicore_id);
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(aicore_id));
  }
  disable_simple_multicore_printf(APU_CORE_5);

  return testcase_finalize();
}
