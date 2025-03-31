// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Virtual Memory Setup for multi-core bare-metal runtime on PVE
// Owner: Manuel Eggimann <manuel.eggimann@axelera.ai>

#include "virtmem_setup.h"

#include <printf.h>
#include <stdint.h>
#include <platform.h>
#include <memorymap.h>
#include <asm.h>
#include <hartids.h>

void setup_virt_l1(sv39_pt_t root_pt,  sv39_pt_t l1_pt) {
  unsigned long hartid, hartid_within_pveX;

  hartid = r_mhartid();
  hartid_within_pveX = hartid - processor_first_hart_id();

  // Set up the root page table (we iterate through the first 512 entries of the
  // root page table (vpn[2] in the RISC-V Sv39 specification)). But we mark all
  // of them as invalid for now.
  for (long vpn_2 = 0; vpn_2 < 512; vpn_2++) {
    unsigned long vpn = vpn_2 << 18;
    // The physical page number is the same as the virtual page number for the
    // idempotent mapping.
    sv39_pte_t    pte = {0};
    pte.fields.ppn    = vpn;
    pte.fields.v      = 1;
    pte.fields.r      = 1;
    pte.fields.w      = 1;
    pte.fields.x      = 1;
    pte.fields.u      = 1;
    // We don't do any page swapping so we set the accessed and dirty bit both to 1.
    pte.fields.a      = 1;
    pte.fields.d      = 1;
    // Set the PTE value for the root page table entry.
    root_pt[vpn_2]    = pte;
  }

  // Now we setup a single second level (mega) page table for the L1 memory. The
  // mapping from virtual to physical address depends on the cluster id (hartid_within_pveX / PVE_CORES_PER_CLUSTER).

  // In each cluster, the first l1_size virtual addresses are mapped to the local L1 of said cluster.
  // The rest of the virtual address space is marked as invalid.
  unsigned long cluster_id = hartid_within_pveX / PVE_NUM_CORES_PER_CLUSTER;
  // The size information is in the address of the symbol, we thus have to get
  // the symbols address and cast it to the desired datatype.
  size_t        l1_size    = (size_t)PVE_0_L1_0_SIZE;

  // The offset between each physical l1 region is the L1 size multiplied by
  // cluster id (in units of 4KiB pages, the pagesize in SV39).
  unsigned long cluster_l1_ppn_offset = l1_size * cluster_id / SV39_PAGESIZE;

  void* l1_start;
  switch(hartid) {
    case AI_CORE_0: {l1_start = (void*)AICORE_0_L1_BASE; break;}
    case AI_CORE_1: {l1_start = (void*)AICORE_1_L1_BASE; break;}
    case AI_CORE_2: {l1_start = (void*)AICORE_2_L1_BASE; break;}
    case AI_CORE_3: {l1_start = (void*)AICORE_3_L1_BASE; break;}
    case AI_CORE_4: {l1_start = (void*)AICORE_4_L1_BASE; break;}
    case AI_CORE_5: {l1_start = (void*)AICORE_5_L1_BASE; break;}
    case AI_CORE_6: {l1_start = (void*)AICORE_6_L1_BASE; break;}
    case AI_CORE_7: {l1_start = (void*)AICORE_7_L1_BASE; break;}
    case PVE_0_CLUSTER_0_CORE_0:
    case PVE_0_CLUSTER_0_CORE_1:
    case PVE_0_CLUSTER_1_CORE_0:
    case PVE_0_CLUSTER_1_CORE_1:
    case PVE_0_CLUSTER_2_CORE_0:
    case PVE_0_CLUSTER_2_CORE_1:
    case PVE_0_CLUSTER_3_CORE_0:
    case PVE_0_CLUSTER_3_CORE_1: {l1_start = (void*)PVE_0_L1_0_BASE; break;}
    case PVE_1_CLUSTER_0_CORE_0:
    case PVE_1_CLUSTER_0_CORE_1:
    case PVE_1_CLUSTER_1_CORE_0:
    case PVE_1_CLUSTER_1_CORE_1:
    case PVE_1_CLUSTER_2_CORE_0:
    case PVE_1_CLUSTER_2_CORE_1:
    case PVE_1_CLUSTER_3_CORE_0:
    case PVE_1_CLUSTER_3_CORE_1: {l1_start = (void*)PVE_1_L1_0_BASE; break;}
  }

  void* l1_end   = l1_start + l1_size;

  sv39_vaddr_t l1_vaddr_start = sv39_ptr_to_vaddr(l1_start);
  sv39_vaddr_t l1_vaddr_end   = sv39_ptr_to_vaddr(l1_end);

  // Set up the mega page table for the L1 memory.
  for (long vpn_1 = 0; vpn_1 < 512; vpn_1++) {
    unsigned long vpn  = l1_vaddr_start.fields.vpn_2 << 18 | vpn_1 << 9;
    // If the virtual page number is within the range of the L1 memory, we map
    // it to the physical address. All other pages stay marked as invalid
    // through the default value of 0.
    sv39_pte_t l1_pte = {0};
    if (vpn_1 >= l1_vaddr_start.fields.vpn_1 && vpn_1 < l1_vaddr_end.fields.vpn_1) {
      // The physical page number is offset by the cluster id times the L1 size.
      l1_pte.fields.ppn = vpn + cluster_l1_ppn_offset;
    } else {
      l1_pte.fields.ppn = vpn;
    }
    l1_pte.fields.v   = 1;
    l1_pte.fields.r   = 1;
    l1_pte.fields.w   = 1;
    l1_pte.fields.x   = 1;
    l1_pte.fields.u   = 1;
    // We don't do any page swapping so we set the accessed and dirty bit both to 1.
    l1_pte.fields.a   = 1;
    l1_pte.fields.d   = 1;
    // Set the PTE value for the mega page table entry.
    l1_pt[vpn_1]      = l1_pte;
  }

  // Reference the second page table in the correct entry of the root page table.
  root_pt[l1_vaddr_start.fields.vpn_2].fields.ppn = ((unsigned long)l1_pt) >> 12;
  // Change flags to indicate that the entry is a pointer to a second level page table.
  root_pt[l1_vaddr_start.fields.vpn_2].fields.v   = 1;
  root_pt[l1_vaddr_start.fields.vpn_2].fields.r   = 0;
  root_pt[l1_vaddr_start.fields.vpn_2].fields.w   = 0;
  root_pt[l1_vaddr_start.fields.vpn_2].fields.x   = 0;
  // Spike triggers a page fault if the following flags are not set to 0 for a second level page table entry.
  root_pt[l1_vaddr_start.fields.vpn_2].fields.u   = 0;
  root_pt[l1_vaddr_start.fields.vpn_2].fields.a   = 0;
  root_pt[l1_vaddr_start.fields.vpn_2].fields.d   = 0;

  // Set the root page table address in the satp register.
  unsigned long root_pt_ppn = ((unsigned long)root_pt) >> 12;
  // Enable Sv39 paging (mode=8) and set the root page table number in the satp register.
  asm volatile("csrw satp, %0" ::"r"(root_pt_ppn | (0x8UL << 60)));
}
