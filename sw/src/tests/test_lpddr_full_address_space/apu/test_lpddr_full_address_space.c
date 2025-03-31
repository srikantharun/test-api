// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Antoine Madec <antoine.madec@axelera.ai>
//        Rodrigo Borges <rodrigo.borges@axelera.ai>
//
// Description: Check that the each LPDDR memory module have 8GB of size by writing/reading in its powers of 2.
//              This test works for both real and fake LPDDR.

#include <lpddr/drv_lpddr.h>
#include <memutils.h>

#define LPDDR_8GB_SIZE (8ll << 30)

int main() {

  uint64_t seed0 = 0xa6009b56f74513df;
  uint64_t seed1 = 0x2972a087ee6ad2d3;
  uintptr_t *forbidden_addresses = NULL;

  testcase_init();

  // TODO: @rodrigo.borges update this macro when more real LPDDR modules are supported
  // Only initialize real LPDDR modules
  #ifdef REAL_LPDDR
    lpddrSubsystemInit(false);
  #endif

  for (int lpddr_module = 0; lpddr_module < 4; lpddr_module++) {
    printf("---- lpddr_graph_%0d\n", lpddr_module);
    mem_write_u64_power_of_2_addresses(
        "LPDDR_0", DDR_0_BASE + lpddr_module * LPDDR_8GB_SIZE,
        LPDDR_8GB_SIZE, seed0 + lpddr_module, forbidden_addresses);

    printf("---- lpddr_ppp_%0d\n", lpddr_module);
    mem_write_u64_power_of_2_addresses(
        "LPDDR_1", DDR_1_BASE + lpddr_module * LPDDR_8GB_SIZE,
        LPDDR_8GB_SIZE, seed1 + lpddr_module, forbidden_addresses);
  }

  for (int lpddr_module = 0; lpddr_module < 4; lpddr_module++) {
    printf("---- lpddr_graph_%0d\n", lpddr_module);
    mem_check_read_u64_power_of_2_addresses(
        "LPDDR_0", DDR_0_BASE + lpddr_module * LPDDR_8GB_SIZE,
        LPDDR_8GB_SIZE, seed0 + lpddr_module, forbidden_addresses);

    printf("---- lpddr_ppp_%0d\n", lpddr_module);
    mem_check_read_u64_power_of_2_addresses(
        "LPDDR_1", DDR_1_BASE + lpddr_module * LPDDR_8GB_SIZE,
        LPDDR_8GB_SIZE, seed1 + lpddr_module, forbidden_addresses);
  }


  return testcase_finalize();
}
