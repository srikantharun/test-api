// check that all RISC-Vs are able to reach all targets memories

#include "test_address_space_memory/address_space_utils.h"
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>

#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <printf.h>

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

  // Forbidden addresses
  uintptr_t forbidden_addresses[] = {}; // Add addresses if test fails at some point.
                                        // For now it works fine!

  // seed configuration
  uint64_t seed_original = 0xa6009b56f74513df;
  uint64_t seed_increment = 0x2d346e84abb9d9dd;

  // Run the memory test
  test_memories(forbidden_addresses, seed_original, seed_increment);

  return testcase_finalize();
}
