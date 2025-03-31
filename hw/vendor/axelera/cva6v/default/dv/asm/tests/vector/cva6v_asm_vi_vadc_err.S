#include "../../env/rag_generated_vector_init.h"

CASE_1_ILLEGAL_MASK_VALUE:
                  vsetvli t0, zero, e32, m1
                  vid.v v1                    # v1 = [0, 1, 2, 3, ...]
                  vmv.v.i v0, 0               # Mask is all 0 → No elements should be added
                  vadc.vvm v2, v1, v1, v0     # Masked, nothing happens
                  vadc.vxm v3, v1, x0, v0     # Masked addition with scalar 0
                  vadc.vim v4, v1, 1, v0      # Masked addition with immediate 1

CASE_2_OVERLAPPING_SOURCE_AND_DESTINATION:
                  vsetvli t0, zero, e32, m1
                  vadc.vvm v1, v1, v1, v0     # Overwrite source register
                  vadc.vxm v1, v1, x0, v0
                  vadc.vim v1, v1, 2, v0

CASE_3_LARGE_CARRY_ADDITION:
                  vsetvli t0, zero, e32, m1
                  li t1, 0xFFFFFFFF           # Max unsigned 32-bit value
                  vmv.v.x v1, t1
                  vadc.vvm v5, v1, v1, v0     # Expect carry-out due to overflow
                  vadc.vxm v5, v1, t1, v0
                  vadc.vim v5, v1, 1, v0

CASE_4_VL_GREATER_THAN_VLMAX:
                  li t0, 150                  # Request VL = 150 elements
                  vsetvli t0, t0, e32
                  vadc.vvm v6, v1, v1, v0     # VL exceeds VLMAX (illegal behavior)
                  vadc.vxm v6, v1, x0, v0
                  vadc.vim v6, v1, 0, v0

CASE_5_RANDOM_MASK_PATTERN:
                  vsetvli t0, zero, e32, m1
                  li t2, 0xAAAA               # Example mask pattern (alternating bits)
                  vmv.v.x v0, t2
                  vadc.vvm v7, v1, v1, v0     # Partial addition due to mask
                  vadc.vxm v7, v1, t2, v0
                  vadc.vim v7, v1, 3, v0

CASE_6_ZERO_VECTOR_ADDITION:
                  vsetvli t0, zero, e32, m1
                  vmv.v.i v8, 0               # Fill v8 with 0
                  vadc.vvm v9, v1, v8, v0     # Result should match v1
                  vadc.vxm v9, v1, x0, v0
                  vadc.vim v9, v1, 0, v0

CASE_7_CARRY_FROM_ALL_ONES:
                  vsetvli t0, zero, e32, m1
                  li t3, -1                   # -1 in two's complement (all bits set)
                  vmv.v.x v1, t3
                  vadc.vvm v10, v1, v1, v0    # Carry generated for every element
                  vadc.vxm v10, v1, t3, v0
                  vadc.vim v10, v1, -1, v0

CASE_8_UNSUPPORTED_SEW:
                  vsetvli t0, zero, e64, m1   # Unsupported SEW for vadc on this hardware
                  vadc.vvm v11, v1, v1, v0
                  vadc.vxm v11, v1, x0, v0
                  vadc.vim v11, v1, 0, v0

CASE_9_UNALIGNED_VL:
                  vsetvli t0, zero, e32, m1
                  li t4, 17                   # Set VL to an odd value
                  vsetvli t0, t4, e32
                  vadc.vvm v12, v1, v1, v0    # Possible misaligned access
                  vadc.vxm v12, v1, x0, v0
                  vadc.vim v12, v1, 0, v0

#include "../../env/rag_generated_vector_end.h"
