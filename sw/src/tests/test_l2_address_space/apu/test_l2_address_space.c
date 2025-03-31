// check that the L2 memory has a defined size of 128 MiB by writing/reading
// in its powers of 2
//
// run accesses twice:
//  1st time: access powers of 2 addresses from the CPU perspective
//  2nd time: access powers of 2 addresses from the L2 perspective (after interleaving)

#include <l2.h>
#include <memorymap.h>
#include <memutils.h>
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>
#include <stdbool.h>
#include <testutils.h>

static uint64_t l2_default_addr_interleaving_cb(uint64_t addr_after_interleaving) {
  return l2_get_addr_before_from_addr_after_interleaving(addr_after_interleaving,
                                                         HW_DEFINES_L2_DEFAULT_INTERLEAVING);
}

int main() {
  uint64_t seed[2] = {0xa6009b56f74513df, 0x0e7871d0b9b87afa};
  uintptr_t *forbidden_addresses = NULL;

  testcase_init();
  pctl_enable_l2();

  for (int apply_interleaving = 0; apply_interleaving < 2; apply_interleaving++) {
    printf("\n---- apply_interleaving = %0d\n", apply_interleaving);

    // write in all power of 2 addresses of each module
    for (uint64_t l2_module_idx = 0; l2_module_idx < HW_DEFINES_L2_MODULE_NUMBER; l2_module_idx++) {
      if (apply_interleaving) {
        mem_write_u64_power_of_2_addresses_with_interleaving(
            "L2", L2_MODULE_0_BASE + l2_module_idx * L2_MODULE_0_SIZE, L2_MODULE_0_SIZE,
            l2_default_addr_interleaving_cb, seed[apply_interleaving] + l2_module_idx,
            forbidden_addresses);
      } else {
        mem_write_u64_power_of_2_addresses(
            "L2", L2_MODULE_0_BASE + l2_module_idx * L2_MODULE_0_SIZE, L2_MODULE_0_SIZE,
            seed[apply_interleaving] + l2_module_idx, forbidden_addresses);
      }
    }

    // check reads in all power of 2 addresses of each module
    for (uint64_t l2_module_idx = 0; l2_module_idx < HW_DEFINES_L2_MODULE_NUMBER; l2_module_idx++) {
      if (apply_interleaving) {
        mem_check_read_u64_power_of_2_addresses_with_interleaving(
            "L2", L2_MODULE_0_BASE + l2_module_idx * L2_MODULE_0_SIZE, L2_MODULE_0_SIZE,
            l2_default_addr_interleaving_cb, seed[apply_interleaving] + l2_module_idx,
            forbidden_addresses);
      } else {
        mem_check_read_u64_power_of_2_addresses(
            "L2", L2_MODULE_0_BASE + l2_module_idx * L2_MODULE_0_SIZE, L2_MODULE_0_SIZE,
            seed[apply_interleaving] + l2_module_idx, forbidden_addresses);
      }
    }
  }

  return testcase_finalize();
}
