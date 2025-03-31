// FIXME: Rodrigo to rename this test and make it work on real LPDDR as well
// check that the LPDDR subsystem should support aligned and unaligned accesses.
// Unaligned accesses are done via masked writes.
//
// test access each LPDDR module and writes/reads 64b/32b/16b/8b words at all the offset of the LPDDR data
// bus size (256b)

#include <memorymap.h>
#include <memutils.h>
#include <pctl/drv_pctl.h>
#include <pctl_utils.h>
#include <stdbool.h>
#include <testutils.h>

int main() {
  uint64_t ddr_byte_data_size = 32;
  uint64_t ddr_module_size = 8ll << 30;

  testcase_init();

  for (int ddr_module = 0; ddr_module < 8; ddr_module++) {
    // FIXME: take interleaving into account when it will be enabled
    uint64_t ddr_module_addr_base = DDR_0_BASE + ddr_module * ddr_module_size;
    uint64_t data_64b = 0xaaaaaaaaaaaaaaaa + ddr_module;
    uint32_t data_32b = 0xbbbbbbbb + ddr_module;
    uint16_t data_16b = 0xcccc + ddr_module;
    uint8_t data_8b = 0xdd + ddr_module;
    for (uint64_t addr_offset = 0; addr_offset < ddr_byte_data_size; addr_offset++) {
      printf("ddr_module=%0d; addr_offset=%0d\n", ddr_module, addr_offset);

      if ((addr_offset % 8) == 0) {
        *(volatile uint64_t *)(ddr_module_addr_base + addr_offset) = data_64b;
      }
      if ((addr_offset % 4) == 0) {
        *(volatile uint32_t *)(ddr_module_addr_base + addr_offset + 8) = data_32b;
      }
      if ((addr_offset % 2) == 0) {
        *(volatile uint16_t *)(ddr_module_addr_base + addr_offset + 12) = data_16b;
      }
      *(volatile uint8_t *)(ddr_module_addr_base + addr_offset + 14) = data_8b;

      if ((addr_offset % 8) == 0) {
        CHECK_EQUAL_HEX(*(volatile uint64_t *)(ddr_module_addr_base + addr_offset), data_64b);
      }
      if ((addr_offset % 4) == 0) {
        CHECK_EQUAL_HEX(*(volatile uint32_t *)(ddr_module_addr_base + addr_offset + 8), data_32b);
      }
      if ((addr_offset % 2) == 0) {
        CHECK_EQUAL_HEX(*(volatile uint16_t *)(ddr_module_addr_base + addr_offset + 12), data_16b);
      }
      CHECK_EQUAL_HEX(*(volatile uint8_t *)(ddr_module_addr_base + addr_offset + 14), data_8b);
    }
  }

  return testcase_finalize();
}
