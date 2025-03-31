// test_l1_frontdoor_access
//
// - Write step:
//  - Calculate the addresses to toggle each address bit of each minibank
//  - For each of this addresses write them as value
// - Read back:
//  - for each of the written addresses, read the value and verify that it is
//    equal to the address accessed

#include <stdint.h>
#include <test_aicore_l1_access/aicore/test_l1_common.h>
#include <testutils.h>
#include <util.h>
#include <cache.h>
#include <uvm_ipc/uvm_sw_ipc.h>

// Write a 128-bit word into L1
// This word consists of the addresses of the 64-bit LSB and MSB
void write_128_bit_word(uintptr_t addr) {
  *(uint64_t *)addr = (uint64_t)addr;
  addr = addr + 8;
  *(uint64_t *)addr = (uint64_t)addr;
}

// Read back the 128-bit word at the specified address
// and verifies each sub-word of 64 bits is equal to its address
void read_and_check_128_bit_word(uintptr_t addr) {
  *(uint64_t *)addr = (uint64_t)addr;
  CHECK_EQUAL_HEX((uint64_t)addr, *(uint64_t *)addr);
  addr = addr + 8;
  CHECK_EQUAL_HEX((uint64_t)addr, *(uint64_t *)addr);
}

void test_l1_frontdoor_access() {

  dcache_disable();

  // Write to the L1 memory at several addresses
  for (uint64_t sb_idx = 0; sb_idx < NB_L1_SUBBANKS; sb_idx++) {
    for (uint64_t mb_idx = 0; mb_idx < NB_L1_MINIBANKS; mb_idx++) {
      // Test the case where all address bits are HIGH (last word)
      // and all address bits are LOW (first word)
      write_128_bit_word(get_addr(sb_idx, mb_idx, 0u));
      write_128_bit_word(
          get_addr(sb_idx, mb_idx, ((uint64_t)1 << MINIBANK_ADDR_WIDTH) - 1u));

      // Toggle address bits 1-by-1
      for (uint64_t addr_bit = 0; addr_bit < MINIBANK_ADDR_WIDTH; addr_bit++) {
        write_128_bit_word(
            get_addr(sb_idx, mb_idx, ((uint64_t)1u << addr_bit)));
      }
    }
  }

  // Read back to the L1 and verify the addresses
  for (uint64_t sb_idx = 0; sb_idx < NB_L1_SUBBANKS; sb_idx++) {
    for (uint64_t mb_idx = 0; mb_idx < NB_L1_MINIBANKS; mb_idx++) {
      read_and_check_128_bit_word(get_addr(sb_idx, mb_idx, 0u));
      read_and_check_128_bit_word(
          get_addr(sb_idx, mb_idx, ((uint64_t)1 << MINIBANK_ADDR_WIDTH) - 1u));

      for (uint64_t addr_bit = 0; addr_bit < MINIBANK_ADDR_WIDTH; addr_bit++) {
        read_and_check_128_bit_word(
            get_addr(sb_idx, mb_idx, ((uint64_t)1u << addr_bit)));
      }
    }
  }

  dcache_enable();
}

int main() {
  testcase_init();

  test_l1_frontdoor_access();

  return testcase_finalize();
}
