// check that the L2 subsystem should support aligned and unaligned accesses.
// Unaligned accesses are done via masked writes.
//
// test access each L2 module and writes/reads 64b/32b/16b/8b words at all the offset of the L2 data
// bus size (512b)

#include <l2.h>
#include <memorymap.h>
#include <memutils.h>
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>
#include <stdbool.h>
#include <testutils.h>

int main() {
  uint64_t l2_byte_data_size = 64;

  testcase_init();
  pctl_enable_l2();

  for (uint64_t l2_module_idx = 0; l2_module_idx < HW_DEFINES_L2_MODULE_NUMBER; l2_module_idx++) {
    uint64_t l2_module_addr_base = l2_get_addr_before_from_addr_after_interleaving(
        L2_MODULE_0_BASE + l2_module_idx * L2_MODULE_0_SIZE, HW_DEFINES_L2_DEFAULT_INTERLEAVING);
    uint64_t data_64b = 0xaaaaaaaaaaaaaaaa + l2_module_idx;
    uint32_t data_32b = 0xbbbbbbbb + l2_module_idx;
    uint16_t data_16b = 0xcccc + l2_module_idx;
    uint8_t data_8b = 0xdd + l2_module_idx;
    for (uint64_t addr_offset = 0; addr_offset < l2_byte_data_size; addr_offset++) {
      printf("l2_module_idx=%0d; addr_offset=%0d\n", l2_module_idx, addr_offset);

      if ((addr_offset % 8) == 0) {
        *(volatile uint64_t *)(l2_module_addr_base + addr_offset) = data_64b;
      }
      if ((addr_offset % 4) == 0) {
        *(volatile uint32_t *)(l2_module_addr_base + addr_offset + 8) = data_32b;
      }
      if ((addr_offset % 2) == 0) {
        *(volatile uint16_t *)(l2_module_addr_base + addr_offset + 12) = data_16b;
      }
      *(volatile uint8_t *)(l2_module_addr_base + addr_offset + 14) = data_8b;

      if ((addr_offset % 8) == 0) {
        CHECK_EQUAL_HEX(*(volatile uint64_t *)(l2_module_addr_base + addr_offset), data_64b);
      }
      if ((addr_offset % 4) == 0) {
        CHECK_EQUAL_HEX(*(volatile uint32_t *)(l2_module_addr_base + addr_offset + 8), data_32b);
      }
      if ((addr_offset % 2) == 0) {
        CHECK_EQUAL_HEX(*(volatile uint16_t *)(l2_module_addr_base + addr_offset + 12), data_16b);
      }
      CHECK_EQUAL_HEX(*(volatile uint8_t *)(l2_module_addr_base + addr_offset + 14), data_8b);
    }
  }

  return testcase_finalize();
}
