#pragma once

#include <asm.h>
#include <hartids.h>
#include <hw_defines.h>

#define UNUSED(x) (void)(x)  // Probably should move that in the future

#define NUM_APU_CORES 6 // Nominal number of APU cores
#define NUM_AICORES   8 // Nominal number of AI cores
#define NUM_PVE_CORES 8 // Nominal number of PVE cores

/*****************************************************************************
 * EXCEPTIONS
 ****************************************************************************/
enum EXCEPTION_SOURCE {
  EXC_INSTRUCTION_ADDRESS_MISALIGNED      = 0,
  EXC_INSTRUCTION_ACCESS_FAULT            = 1,
  EXC_ILLEGAL_INSTRUCTION                 = 2,
  EXC_BREAKPOINT                          = 3,
  EXC_LOAD_ADDRESS_MISALIGNED             = 4,
  EXC_LOAD_ACCESS_FAULT                   = 5,
  EXC_STORE_AMO_ADDRESS_MISALIGNED        = 6,
  EXC_STORE_AMO_ACCESS_FAULT              = 7,
  EXC_ENVIRONMENT_CALL_FROM_U_MODE        = 8,
  EXC_ENVIRONMENT_CALL_FROM_S_MODE        = 9,
  EXC_RESERVED_1                          = 10,
  EXC_ENVIRONMENT_CALL_FROM_M_MODE        = 11,
  EXC_INSTRUCTION_PAGE_FAULT              = 12,
  EXC_LOAD_PAGE_FAULT                     = 13,
  EXC_RESERVED_2                          = 14,
  EXC_STORE_AMO_PAGE_FAULT                = 15,
  NUM_EXCEPTION_SOURCE
};


/* HARD_IDs per core */
#define SW_IRQ_TOTAL PVE_0_CLUSTER_0_CORE_0

/* shared initialization functions for all processors */
void _init_bss();
void _init_tls();

/* pre-declare to avoid circular include */
__attribute__((noreturn)) void abort();

/* returns the first HART id for the current processor */
static inline uint64_t processor_first_hart_id() {
  uint64_t hart_id = r_mhartid();
#ifdef SYSTEM_CVA6V
  // single-core system
  return hart_id;
#else
  if (hart_id <= APU_CORE_5) {
      // APU
      return APU_CORE_0;
  }
  if (hart_id <= AI_CORE_7) {
      // AI cores
      return hart_id;
  }
  if (hart_id <= PVE_0_CLUSTER_3_CORE_1) {
      // PVE 0
      return PVE_0_CLUSTER_0_CORE_0;
  }
  if (hart_id <= PVE_1_CLUSTER_3_CORE_1) {
      // PVE 1
      return PVE_1_CLUSTER_0_CORE_0;
  }
  abort();
#endif
}
