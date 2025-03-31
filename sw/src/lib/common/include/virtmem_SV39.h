// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Virtual Memory Setup for multi-core bare-metal runtime on PVE
// Owner: Manuel Eggimann <manuel.eggimann@axelera.ai>

#include <stddef.h>
#include <stdint.h>


typedef union __attribute__((packed)) __attribute__((aligned(8))) {
  struct __attribute__((packed)) {
    _Bool        v : 1;         //< PTE valid bit
    _Bool        r : 1;         //< Page readable bit
    _Bool        w : 1;         //< Page writable bit
    _Bool        x : 1;         //< Page executable bit
    _Bool        u : 1;         //< Page accessible from user mode bit
    _Bool        g : 1;         //< Global page bit
    _Bool        a : 1;         //< Accessed bit
    _Bool        d : 1;         //< Dirty bit
    unsigned int rsw : 2;       //< Reserved for software
    uint64_t     ppn : 44;      //< Physical page number
    unsigned int reserved : 7;  //< Reserved
    unsigned int pbmt : 2;  //< Page-based memory type (reserved and must be zeroed by software if Svpbmt extension is
                            // not supported)
    _Bool n : 1;  //< NAPOT (Naturally Aligned Power Of Two) bit (must be zeroed by software if Svnapot extension is not
                  // supported)
  } fields;
  uint64_t value;
} sv39_pte_t;

typedef union __attribute__((packed)) {
  struct __attribute__((packed)) {
    uint32_t offset : 12;
    uint32_t vpn_0 : 9;
    uint32_t vpn_1 : 9;
    uint32_t vpn_2 : 9;
  } fields;
  uint64_t value;
} sv39_vaddr_t;

static inline void* sv39_vaddr_to_ptr(sv39_vaddr_t vaddr) {
  // The Sv39 standard requires bits 63:39 to be equal (sign-extended) from bit
  // 26 of the virtual page number (vpn) (see RISC-V Privileged Architecture
  // specification).
  int64_t addr = (int64_t)((vaddr.fields.vpn_2 << 27) | (vaddr.fields.vpn_1 << 18) | (vaddr.fields.vpn_0 << 9) |
                           vaddr.fields.offset);
  return (void*)((addr << 25) >> 25);
}

static inline sv39_vaddr_t sv39_ptr_to_vaddr(void* ptr) {
  sv39_vaddr_t vaddr = {.value = (uint64_t)ptr};
  return vaddr;
}

typedef sv39_pte_t sv39_pt_t[512];

#define SV39_PAGESIZE 4096

// thread_local_noinit __attribute__((aligned(SV39_PAGESIZE))) sv39_pt_t root_pt;
// // Second level page table for the L1 memory region
// thread_local_noinit __attribute__((aligned(SV39_PAGESIZE))) sv39_pt_t l1_pt;

// /**
//  * Set up the page tables for the virtual memory system.
//  *
//  * Since each cluster has its own L1 memory, we leverage virtual address
//  * translation to map the physical address of the L1 memory to the same virtual
//  * address region. That way, we can use the same binary for all cores.
//  *
//  * Except for the L1 region, the rest of the memory is idempotently (virtual ==
//  * physical address) mapped.
//  *
//  */
// no_instrument void setup_virtmem(void);
