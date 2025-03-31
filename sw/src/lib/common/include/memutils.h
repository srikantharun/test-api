// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

/**
 * Description: Functions to check memories
 */

#pragma once

#include <rng.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <trex/trex_utils.h>

typedef enum { SNPS, AXE } dma_type_e;

// write pseudo random values in memory's power of 2 addresses
void mem_write_u64_power_of_2_addresses(const char *mem_name, uintptr_t addr_base,
                                        uint64_t addr_size, uint64_t seed,
                                        uintptr_t *forbidden_addresses);

// read and check expected values in memory's power of 2 addresses
void mem_check_read_u64_power_of_2_addresses(const char *mem_name, uintptr_t addr_base,
                                             uint64_t addr_size, uint64_t seed,
                                             uintptr_t *forbidden_addresses);

// write pseudo random values in memory's power of 2 addresses,
// apply interleaving callback to the address
void mem_write_u64_power_of_2_addresses_with_interleaving(
    const char *mem_name, uintptr_t addr_base, uint64_t addr_size,
    uint64_t (*addr_interleaving_cb)(uint64_t), uint64_t seed, uintptr_t *forbidden_addresses);

// read and check expected values in memory's power of 2 addresses,
// apply interleaving callback to the address
void mem_check_read_u64_power_of_2_addresses_with_interleaving(
    const char *mem_name, uintptr_t addr_base, uint64_t addr_size,
    uint64_t (*addr_interleaving_cb)(uint64_t), uint64_t seed, uintptr_t *forbidden_addresses);

// write pseudo random values in memory's power of 2 addresses with the DMA,
// `dma_src -> mem(addr_base, addr_size)` where `dma_src` is initially populated by the CPU in a
// contiguous manner
void mem_write_dma_power_of_2_addresses(dma_type_e dma_type, char *dma_name,
                                        uintptr_t dma_src_addr_base, const char *mem_name,
                                        uintptr_t addr_base, uint64_t addr_size, uint64_t seed,
                                        uintptr_t *forbidden_addresses);

// read and check expected values in memory's power of 2 addresses with the DMA,
// `mem(addr_base, addr_size) -> dma_dst` where `dma_dst` is written in a contiguous manner
void mem_check_read_dma_power_of_2_addresses(dma_type_e dma_type, char *dma_name,
                                             uintptr_t dma_dst_addr_base, const char *mem_name,
                                             uintptr_t addr_base, uint64_t addr_size, uint64_t seed,
                                             uintptr_t *forbidden_addresses);

// Compare memory and provide useful log, x and y must be aligned to 8 bytes,
// n_bytes and offset must be multiple of 8
void mem_check_equal(const char *x, const char *y, int offset, int n_bytes, const char *msg);

// Function to populate forbidden addresses for multiple regions
void populate_forbidden_addresses(uintptr_t *forbidden_addresses, uintptr_t ranges[][2],
                                  int num_ranges);
