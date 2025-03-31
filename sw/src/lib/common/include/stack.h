#pragma once

/* APU: 128 KiB per core */
#define APU_STACK_SHIFT 17
#define APU_STACK_SIZE (1 << APU_STACK_SHIFT)

/* AICORE: 16 KiB */
#define AICORE_STACK_SHIFT 14
#define AICORE_STACK_SIZE  (1 << AICORE_STACK_SHIFT)

/* PVE: 16 KiB per core */
#define PVE_STACK_SHIFT 14
#define PVE_STACK_SIZE  (1 << PVE_STACK_SHIFT)

/* CVA6V standalone: 128 KiB per core */
/* WARNING: This is hard-coded in cva6v/link.ld, which needs to be kept in sync
 *          when updating this. */
#define CVA6V_STANDALONE_STACK_SHIFT 17
#define CVA6V_STANDALONE_STACK_SIZE  (1 << CVA6V_STANDALONE_STACK_SHIFT)
