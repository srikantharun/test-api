#pragma once

#include "virtmem_SV39.h"

// __thread __attribute__((aligned(SV39_PAGESIZE))) sv39_pt_t root_pt;
// // Second level page table for the L1 memory region
// __thread __attribute__((aligned(SV39_PAGESIZE))) sv39_pt_t l1_pt;

/**
 * Set up the page tables for the virtual memory system.
 *
 * Since each cluster has its own L1 memory, we leverage virtual address
 * translation to map the physical address of the L1 memory to the same virtual
 * address region. That way, we can use the same binary for all cores.
 *
 * Except for the L1 region, the rest of the memory is idempotently (virtual ==
 * physical address) mapped.
 *
 */
void setup_virt_l1(sv39_pt_t root_pt,  sv39_pt_t l1_pt);
