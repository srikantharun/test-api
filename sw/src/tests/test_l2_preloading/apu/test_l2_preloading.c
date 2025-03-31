// basic test checking l2 buffers can be loaded and read properly

#include "hw_defines.h"
#include <l2.h>
#include <memorymap.h>
#include <pctl_utils.h>
#include <testutils.h>

extern uint64_t l2_buffer[L2_SIZE] __attribute__((section(".l2")));

int main() {
  testcase_init();

  pctl_enable_l2();

  for (uint64_t module = 0; module < HW_DEFINES_L2_MODULE_NUMBER; module++) {
    for (uint64_t bank = 0; bank < L2_NUM_BANKS; bank++) {
      for (uint64_t ram = 0; ram < L2_NUM_RAMS; ram++) {
        for (uint64_t sram = 0; sram < L2_NUM_SRAMS; sram++) {
          uint64_t sram_8B_word_addr = 0;
          uint64_t logical_address =
              l2_get_addr_before_interleaving_from_physical(
                  module, bank, ram, sram_8B_word_addr, sram,
                  HW_DEFINES_L2_DEFAULT_INTERLEAVING);
          uint64_t rdata = *(uint64_t *)logical_address;
          printf("0x%016lx <- [0x%010lx] (L2 module=%0d,bank=%0d,ram=%0d,"
                 "sram_addr=%0d,sram=%0d,inter=%0d)\n",
                 rdata, logical_address, module, bank, ram, sram_8B_word_addr,
                 sram, HW_DEFINES_L2_DEFAULT_INTERLEAVING);
          CHECK_EQUAL_HEX(rdata, logical_address);
        }
      }
    }
  }

  return testcase_finalize();
}
