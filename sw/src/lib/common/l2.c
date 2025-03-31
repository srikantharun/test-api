// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "testutils.h"
#include <l2.h>
#include <memorymap.h>
#include <std/std_bit.h>

const uint64_t L2_NUM_MODULES = 8;
const uint64_t L2_NUM_BANKS = 16;
const uint64_t L2_NUM_RAMS = 4;
const uint64_t L2_NUM_SRAMS = 4;
const uint64_t L2_NUM_SRAM_8B_WORDS = 4096;

uint64_t l2_get_addr_before_from_addr_after_interleaving(
    uint64_t addr_after_interleaving, l2_interleaving_t interleaving) {
  uint64_t module = BIT_READ_SELECT(addr_after_interleaving, 26, 24);
  uint64_t addr_in_module = BIT_READ_SELECT(addr_after_interleaving, 23, 0);
  uint64_t addr_relative_before;
  if (interleaving == CONTIGUOUS) {
    return addr_after_interleaving;
  } else if (interleaving == INTER_1X8_1K) {
    addr_relative_before = BIT_READ_SELECT(addr_in_module, 9, 0) + (module << 10) +
                           (BIT_READ_SELECT(addr_in_module, 23, 13) << 13) +
                           (BIT_READ_SELECT(addr_in_module, 12, 10) << 24);
  } else if (interleaving == INTER_1X8_2K) {
    addr_relative_before = BIT_READ_SELECT(addr_in_module, 10, 0) + (module << 11) +
                           (BIT_READ_SELECT(addr_in_module, 23, 14) << 14) +
                           (BIT_READ_SELECT(addr_in_module, 13, 11) << 24);
  } else if (interleaving == INTER_1X8_4K) {
    addr_relative_before = BIT_READ_SELECT(addr_in_module, 11, 0) + (module << 12) +
                           (BIT_READ_SELECT(addr_in_module, 23, 15) << 15) +
                           (BIT_READ_SELECT(addr_in_module, 14, 12) << 24);
  } else {
    ASSERT(0, "interleaving=%0d is not supported yet", interleaving);
  }
  return L2_BASE + addr_relative_before;
}

uint64_t l2_get_addr_after_interleaving_from_physical(
    uint64_t module, uint64_t bank, uint64_t ram, uint64_t sram_8B_word_addr,
    uint64_t sram) {
  // module = addr[26:24]
  // bank = addr[23:20]
  // ram = addr[19:18]
  // sram_word_address = addr[17:6]
  // sram = addr[5:4]
  return L2_BASE + (module << 24) + (bank << 20) + (ram << 18) +
         (sram_8B_word_addr << 6) + (sram << 4);
}

uint64_t l2_get_addr_before_interleaving_from_physical(
    uint64_t module, uint64_t bank, uint64_t ram, uint64_t sram_8B_word_addr,
    uint64_t sram, l2_interleaving_t interleaving) {
  uint64_t addr_after_interleaving;
  uint64_t addr_before_interleaving;
  addr_after_interleaving = l2_get_addr_after_interleaving_from_physical(
      module, bank, ram, sram_8B_word_addr, sram);
  addr_before_interleaving = l2_get_addr_before_from_addr_after_interleaving(
      addr_after_interleaving, interleaving);
  return addr_before_interleaving;
}
