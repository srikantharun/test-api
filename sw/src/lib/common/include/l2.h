// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: utils to set L2 interleaving and navigate address conversion
//
// addr_before_interleaving->[NOC]->addr_after_interleaving->[L2]->physical
//
// Documentation:
// https://doc.axelera.ai/prod/europa/latest/europa/blocks/noc/#l2-interleaving
// https://doc.axelera.ai/prod/europa/latest/europa_architecture/blocks/noc/network-on-chip/#l2-mapping

#pragma once

#include <stdint.h>

extern const uint64_t L2_NUM_MODULES;
extern const uint64_t L2_NUM_BANKS;
extern const uint64_t L2_NUM_RAMS;
extern const uint64_t L2_NUM_SRAMS;
extern const uint64_t L2_NUM_SRAM_8B_WORDS;

typedef enum {
  CONTIGUOUS = 0,
  INTER_1X8_1K,
  INTER_1X8_2K,
  INTER_1X8_4K,
  INTER_2X4_1K,
  INTER_2X4_2K,
  INTER_2X4_4K,
} l2_interleaving_t;

// get address after interleaving from physical address
// `addr_before_interleaving->[NOC]->addr_after_interleaving->[L2]->physical`
uint64_t l2_get_addr_after_interleaving_from_physical(
    uint64_t module, uint64_t bank, uint64_t ram, uint64_t sram_8B_word_addr,
    uint64_t sram);

// get address before interleaving from address after interleaving
// `addr_before_interleaving->[NOC]->addr_after_interleaving->[L2]->physical`
uint64_t l2_get_addr_before_from_addr_after_interleaving(
    uint64_t addr_after_interleaving, l2_interleaving_t interleaving);

// get address before interleaving from physical address:
// `addr_before_interleaving->[NOC]->addr_after_interleaving->[L2]->physical`
uint64_t l2_get_addr_before_interleaving_from_physical(
    uint64_t module, uint64_t bank, uint64_t ram, uint64_t sram_8B_word_addr,
    uint64_t sram, l2_interleaving_t interleaving);
