// check that LP_DMA_APU is able to reach all its targets memories
//
// scenario:
//  1. for each memory: DMA(dma_src -> mem)
//  2. for each memory: DMA(dma_dst <- mem)
//  data in dma_src and dma_dst are populated and checked by the CPU

#include "test_address_space_memory/address_space_utils.h"
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>

#include <multicore.h>
#include <platform.h>
#include <printf.h>
#include <testutils.h>
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
  for (uint32_t i = AI_CORE_0; i < (AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER); i++) {
    pctl_enable_aicore(i);
  }

  // Forbidden addresses
  uintptr_t forbidden_addresses[] = {
      0x0007004000, // code in SYS SPM
      0x0007008000, // code in SYS SPM
      0,
  };

  // seed configuration
  uint64_t seed_original = 0xa6009b56f74513df;
  uint64_t seed_increment = 0x2d346e84abb9d9dd;

  // Run the memory test
  test_memories_with_dma(SNPS, "LP_DMA_APU", forbidden_addresses, seed_original, seed_increment);

  return testcase_finalize();
}
