#include "../../env/rag_generated_vector_init.h"

CASE_1_ILLEGAL_MASK_VALUE:
                  vsetvli t0, zero, e32, m1
                  vid.v v1                    # v1 = [0, 1, 2, 3, ...]
                  vmv.v.i v0, 0               # Mask is all 0
                  vadd.vv v2, v1, v1, v0.t
                  vadd.vx v3, v1, x0, v0.t
                  vadd.vi v4, v1, 0, v0.t

CASE_2_OVERLAPPING_SOURCE_AND_DESTINATION:
                  vsetvli t0, zero, e32, m1
                  vadd.vv v1, v1, v1
                  vadd.vx v1, v1, x0
                  vadd.vi v1, v1, 0

CASE_3_VL_GREATER_THAN_VLMAX:
                  li t0, 150
                  vsetvli t0, t0, e32
                  vadd.vv v3, v1, v1
                  vadd.vx v3, v1, x0
                  vadd.vi v3, v1, 0

CASE_4_LARGE_INTEGER_OVERFLOW:
                  vsetvli t0, zero, e32, m1
                  li t2, 0x7FFFFFFF
                  vmv.v.x v1, t2
                  vadd.vv v4, v1, v1
                  vadd.vx v4, v1, t2
                  vadd.vi v4, v1, 1

CASE_5_NEGATIVE_VALUE_ADDITION:
                  vsetvli t0, zero, e32, m1
                  li t3, -1
                  vmv.v.x v1, t3
                  vadd.vv v5, v1, v1
                  vadd.vx v5, v1, t3
                  vadd.vi v5, v1, -1

CASE_6_RANDOM_MASK_PATTERN:
                  vsetvli t0, zero, e32, m1
                  li t4, 0xAAAA
                  vmv.v.x v0, t4
                  vadd.vv v6, v1, v1, v0.t
                  vadd.vx v6, v1, x0, v0.t
                  vadd.vi v6, v1, 0, v0.t

CASE_7_DIFFERENT_LMUL_CONFIGURATIONS:
                  vsetvli t0, zero, e32, m8
                  vadd.vv v7, v1, v1
                  vadd.vx v7, v1, x0
                  vadd.vi v7, v1, 0

CASE_8_ZERO_VECTOR_ADDITION:
                  vsetvli t0, zero, e32, m1
                  vmv.v.i v8, 0
                  vadd.vv v9, v1, v8
                  vadd.vx v9, v1, x0
                  vadd.vi v9, v1, 0

CASE_9_ILLEGAL_VECTOR_LENGTH:
                  vsetvli t0, zero, e32, m1
                  li t1, 0
                  vsetvli t0, t1, e32
                  vadd.vv v10, v1, v1
                  vadd.vx v10, v1, x0
                  vadd.vi v10, v1, 0

CASE_10_VL_EXCEEDS_VLMAX:
                  vsetvli t0, zero, e32, m1
                  li t1, 1024
                  vsetvli t0, t1, e32
                  vadd.vv v11, v1, v1
                  vadd.vx v11, v1, x0
                  vadd.vi v11, v1, 0

CASE_11_UNSUPPORTED_SEW:
                  vsetvli t0, zero, e64, m1
                  vadd.vv v12, v1, v1
                  vadd.vx v12, v1, x0
                  vadd.vi v12, v1, 0

CASE_12_MASKED_VECTOR_WITH_INSUFFICIENT_ELEMENTS:
                  vsetvli t0, zero, e32, m1
                  li t2, 0xF0F0F0F0
                  vmv.v.x v0, t2
                  vadd.vv v13, v1, v1, v0.t
                  vadd.vx v13, v1, x0, v0.t
                  vadd.vi v13, v1, 0, v0.t

CASE_13_INSUFFICIENT_REGISTER_WIDTH:
                  vsetvli t0, zero, e16, m1
                  li t3, 0xFFFF
                  vmv.v.x v1, t3
                  vadd.vv v14, v1, v1
                  vadd.vx v14, v1, x0
                  vadd.vi v14, v1, 1

CASE_14_UNALIGNED_ELEMENTS:
                  vsetvli t0, zero, e32, m1
                  li t4, 0x1
                  vmv.v.x v1, t4
                  vadd.vv v15, v1, v1
                  vadd.vx v15, v1, x0
                  vadd.vi v15, v1, 0

CASE_15_FULL_MASK_NO_ELEMENTS_SKIPPED:
                  vsetvli t0, zero, e32, m1
                  li t5, 0xFFFFFFFF
                  vmv.v.x v0, t5
                  vadd.vv v16, v1, v1, v0.t
                  vadd.vx v16, v1, x0, v0.t
                  vadd.vi v16, v1, 0, v0.t

CASE_16_INSUFFICIENT_VECTOR_REGISTERS:
                  vsetvli t0, zero, e32, m1
                  vadd.vv v17, v1, v1
                  vadd.vx v17, v1, x0
                  vadd.vi v17, v1, 0

CASE_17_ADDITION_WITH_ALL_ZEROS:
                  vsetvli t0, zero, e32, m1
                  vmv.v.i v1, 0
                  vadd.vv v18, v1, v1
                  vadd.vx v18, v1, x0
                  vadd.vi v18, v1, 0

#include "../../env/rag_generated_vector_end.h"
