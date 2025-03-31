// Adapted from https://github.com/Tencent/ncnn/blob/master/src/layer/riscv/rvv_mathfun_fp16s.h
// Tencent is pleased to support the open source community by making ncnn
// available.
//
// Copyright (C) 2021 THL A29 Limited, a Tencent company. All rights reserved.
//
// Licensed under the BSD 3-Clause License (the "License"); you may not use this
// file except in compliance with the License. You may obtain a copy of the
// License at
//
// https://opensource.org/licenses/BSD-3-Clause
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations under
// the License.

#pragma once

#include <riscv_vector.h>

#define c_inv_mant_mask_f16 -31745  // ~0x7c00u
#define c_cephes_SQRTHF     0.707106781186547524f
#define c_cephes_log_p0     7.0376836292E-2f
#define c_cephes_log_p1     -1.1514610310E-1f
#define c_cephes_log_p2     1.1676998740E-1f
#define c_cephes_log_p3     -1.2420140846E-1f
#define c_cephes_log_p4     +1.4249322787E-1f
#define c_cephes_log_p5     -1.6668057665E-1f
#define c_cephes_log_p6     +2.0000714765E-1f
#define c_cephes_log_p7     -2.4999993993E-1f
#define c_cephes_log_p8     +3.3333331174E-1f
#define c_cephes_log_q1     -2.12194440e-4f
#define c_cephes_log_q2     0.693359375f

#define _RVV_FLOAT16_LOG_OP(LMUL, MLEN)                                                                           \
  static inline vfloat16m##LMUL##_t log_ps_f16m##LMUL(vfloat16m##LMUL##_t x, uint32_t vl) {                       \
    x                            = __riscv_vfmax_vf_f16m##LMUL(x, 0.f, vl); /* force flush to zero on denormal */ \
    vbool##MLEN##_t invalid_mask = __riscv_vmfle_vf_f16m##LMUL##_b##MLEN(x, 0.f, vl);                             \
                                                                                                                  \
    vint16m##LMUL##_t ux = __riscv_vreinterpret_v_f16m##LMUL##_i16m##LMUL(x);                                     \
                                                                                                                  \
    vint16m##LMUL##_t emm0 = __riscv_vsra_vx_i16m##LMUL(ux, 10, vl);                                              \
                                                                                                                  \
    /* keep only the fractional part */                                                                           \
    ux = __riscv_vand_vx_i16m##LMUL(ux, c_inv_mant_mask_f16, vl);                                                 \
    ux = __riscv_vor_vx_i16m##LMUL(ux, 14336 /* reinterpret_cast<short>((__fp16)0.5) */, vl);                     \
    x  = __riscv_vreinterpret_v_i16m##LMUL##_f16m##LMUL(ux);                                                      \
                                                                                                                  \
    emm0                  = __riscv_vsub_vx_i16m##LMUL(emm0, 0xf, vl);                                            \
    vfloat16m##LMUL##_t e = __riscv_vfcvt_f_x_v_f16m##LMUL(emm0, vl);                                             \
                                                                                                                  \
    e = __riscv_vfadd_vf_f16m##LMUL(e, 1.f, vl);                                                                  \
                                                                                                                  \
    /* part2:                      */                                                                             \
    /*     if( x < SQRTHF ) {      */                                                                             \
    /*       e -= 1;               */                                                                             \
    /*       x = x + x - 1.0;      */                                                                             \
    /*     } else { x = x - 1.0; } */                                                                             \
    vbool##MLEN##_t mask = __riscv_vmflt_vf_f16m##LMUL##_b##MLEN(x, c_cephes_SQRTHF, vl);                         \
    x                    = __riscv_vfadd_vv_f16m##LMUL##_mu(mask, x, x, x, vl);                                   \
    x                    = __riscv_vfsub_vf_f16m##LMUL(x, 1.f, vl);                                               \
    e                    = __riscv_vfsub_vf_f16m##LMUL##_mu(mask, e, e, 1.f, vl);                                 \
                                                                                                                  \
    vfloat16m##LMUL##_t z = __riscv_vfmul_vv_f16m##LMUL(x, x, vl);                                                \
                                                                                                                  \
    vfloat16m##LMUL##_t y = __riscv_vfmul_vf_f16m##LMUL(x, c_cephes_log_p0, vl);                                  \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p1, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p2, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p3, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p4, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p5, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p6, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p7, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_log_p8, vl);                                  \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                \
                                                                                                                  \
    y = __riscv_vfmul_vv_f16m##LMUL(y, z, vl);                                                                    \
                                                                                                                  \
    vfloat16m##LMUL##_t tmp = __riscv_vfmul_vf_f16m##LMUL(e, c_cephes_log_q1, vl);                                \
    y                       = __riscv_vfadd_vv_f16m##LMUL(y, tmp, vl);                                            \
                                                                                                                  \
    tmp = __riscv_vfmul_vf_f16m##LMUL(z, 0.5f, vl);                                                               \
    y   = __riscv_vfsub_vv_f16m##LMUL(y, tmp, vl);                                                                \
                                                                                                                  \
    tmp                     = __riscv_vfmul_vf_f16m##LMUL(e, c_cephes_log_q2, vl);                                \
    x                       = __riscv_vfadd_vv_f16m##LMUL(x, y, vl);                                              \
    x                       = __riscv_vfadd_vv_f16m##LMUL(x, tmp, vl);                                            \
    /* negative arg will be NAN */                                                                                \
    vuint16m##LMUL##_t xtmp = __riscv_vreinterpret_v_f16m##LMUL##_u16m##LMUL(x);                                  \
    xtmp                    = __riscv_vor_vx_u16m##LMUL##_mu(invalid_mask, xtmp, xtmp, 0xffff, vl);               \
    x                       = __riscv_vreinterpret_v_u16m##LMUL##_f16m##LMUL(xtmp);                               \
    return x;                                                                                                     \
  }

_RVV_FLOAT16_LOG_OP(1, 16)
_RVV_FLOAT16_LOG_OP(2, 8)
_RVV_FLOAT16_LOG_OP(4, 4)
_RVV_FLOAT16_LOG_OP(8, 2)

#define c_exp_hi_f16 10.7421875f
#define c_exp_lo_f16 -10.7421875f

#define c_cephes_LOG2EF 1.44269504088896341
#define c_cephes_exp_C1 0.693359375
#define c_cephes_exp_C2 -2.12194440e-4

#define c_cephes_exp_p0 1.9875691500E-4
#define c_cephes_exp_p1 1.3981999507E-3
#define c_cephes_exp_p2 8.3334519073E-3
#define c_cephes_exp_p3 4.1665795894E-2
#define c_cephes_exp_p4 1.6666665459E-1
#define c_cephes_exp_p5 5.0000001201E-1

// This macro takes the following approach:
// https://github.com/jeremybarnes/cephes/blob/master/cmath/exp.c
// The original code has been adapted to handle the infinity case
// correctly.

#define _RVV_FLOAT16_EXP_OP(LMUL, MLEN)                                                               \
  static inline vfloat16m##LMUL##_t exp_ps_f16m##LMUL(vfloat16m##LMUL##_t x, uint32_t vl) {           \
    vfloat16m##LMUL##_t tmp, fx;                                                                      \
                                                                                                      \
    x = __riscv_vfmin_vf_f16m##LMUL(x, c_exp_hi_f16, vl);                                             \
    x = __riscv_vfmax_vf_f16m##LMUL(x, c_exp_lo_f16, vl);                                             \
                                                                                                      \
    /* express exp(x) as exp(g + n*log(2)) */                                                         \
    fx = __riscv_vfmacc_vf_f16m##LMUL(__riscv_vfmv_v_f_f16m##LMUL(0.5f, vl), c_cephes_LOG2EF, x, vl); \
                                                                                                      \
    /* perform a floorf */                                                                            \
    tmp = __riscv_vfcvt_f_x_v_f16m##LMUL(__riscv_vfcvt_x_f_v_i16m##LMUL(fx, vl), vl);                 \
                                                                                                      \
    /* if greater, substract 1 */                                                                     \
    vbool##MLEN##_t mask = __riscv_vmfgt_vv_f16m##LMUL##_b##MLEN(tmp, fx, vl);                        \
    fx                   = __riscv_vfsub_vf_f16m##LMUL##_mu(mask, tmp, tmp, 1.f, vl);                 \
                                                                                                      \
    tmp                   = __riscv_vfmul_vf_f16m##LMUL(fx, c_cephes_exp_C1, vl);                     \
    vfloat16m##LMUL##_t z = __riscv_vfmul_vf_f16m##LMUL(fx, c_cephes_exp_C2, vl);                     \
    mask                  = __riscv_vmfeq_vf_f16m##LMUL##_b##MLEN(x, c_exp_hi_f16, vl);               \
    x                     = __riscv_vfsub_vv_f16m##LMUL(x, tmp, vl);                                  \
    x                     = __riscv_vfsub_vv_f16m##LMUL(x, z, vl);                                    \
                                                                                                      \
    vfloat16m##LMUL##_t y = __riscv_vfmul_vf_f16m##LMUL(x, c_cephes_exp_p0, vl);                      \
    z                     = __riscv_vfmul_vv_f16m##LMUL(x, x, vl);                                    \
                                                                                                      \
    y = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_exp_p1, vl);                                          \
    y = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                        \
    y = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_exp_p2, vl);                                          \
    y = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                        \
    y = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_exp_p3, vl);                                          \
    y = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                        \
    y = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_exp_p4, vl);                                          \
    y = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                        \
    y = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_exp_p5, vl);                                          \
                                                                                                      \
    y = __riscv_vfmul_vv_f16m##LMUL(y, z, vl);                                                        \
    y = __riscv_vfadd_vv_f16m##LMUL(y, x, vl);                                                        \
    y = __riscv_vfadd_vf_f16m##LMUL(y, 1.f, vl);                                                      \
                                                                                                      \
    /* build 2^n */                                                                                   \
    vint16m##LMUL##_t mm      = __riscv_vfcvt_x_f_v_i16m##LMUL(fx, vl);                               \
    mm                        = __riscv_vadd_vx_i16m##LMUL(mm, 0xf, vl);                              \
    mm                        = __riscv_vsll_vx_i16m##LMUL(mm, 10, vl);                               \
    vfloat16m##LMUL##_t pow2n = __riscv_vreinterpret_v_i16m##LMUL##_f16m##LMUL(mm);                   \
                                                                                                      \
    y           = __riscv_vfmul_vv_f16m##LMUL(y, pow2n, vl);                                          \
    int16_t inf = 0x7C00;                                                                             \
    y           = __riscv_vfmerge_vfm_f16m##LMUL(y, *(_Float16 *)&inf, mask, vl);                     \
    return y;                                                                                         \
  }

_RVV_FLOAT16_EXP_OP(1, 16)
_RVV_FLOAT16_EXP_OP(2, 8)
_RVV_FLOAT16_EXP_OP(4, 4)
_RVV_FLOAT16_EXP_OP(8, 2)

#define c_minus_cephes_DP1 -0.78515625
#define c_minus_cephes_DP2 -2.4187564849853515625e-4
#define c_minus_cephes_DP3 -3.77489497744594108e-8
#define c_sincof_p0        -1.9515295891E-4
#define c_sincof_p1        8.3321608736E-3
#define c_sincof_p2        -1.6666654611E-1
#define c_coscof_p0        2.443315711809948E-005
#define c_coscof_p1        -1.388731625493765E-003
#define c_coscof_p2        4.166664568298827E-002
#define c_cephes_FOPI      1.27323954473516  // 4 / M_PI

#define _RVV_FLOAT16_SINCOS_OP(LMUL, MLEN)                                                                             \
  static inline void sincos_ps_f16m##LMUL(vfloat16m##LMUL##_t x, vfloat16m##LMUL##_t *ysin, vfloat16m##LMUL##_t *ycos, \
                                          uint32_t vl) {                                                               \
    /* any x */                                                                                                        \
    vfloat16m##LMUL##_t xmm1, xmm2, xmm3, y;                                                                           \
                                                                                                                       \
    vuint16m##LMUL##_t emm2;                                                                                           \
                                                                                                                       \
    vbool##MLEN##_t sign_mask_sin, sign_mask_cos;                                                                      \
    sign_mask_sin = __riscv_vmflt_vf_f16m##LMUL##_b##MLEN(x, 0.f, vl);                                                 \
    x             = __riscv_vfsgnj_vf_f16m##LMUL(x, 1.f, vl);                                                          \
                                                                                                                       \
    /* scale by 4/Pi */                                                                                                \
    y = __riscv_vfmul_vf_f16m##LMUL(x, c_cephes_FOPI, vl);                                                             \
                                                                                                                       \
    /* store the integer part of y in mm0 */                                                                           \
    emm2 = __riscv_vfcvt_xu_f_v_u16m##LMUL(y, vl);                                                                     \
    /* j=(j+1) & (~1) (see the cephes sources) */                                                                      \
    emm2 = __riscv_vadd_vx_u16m##LMUL(emm2, 1, vl);                                                                    \
    emm2 = __riscv_vand_vx_u16m##LMUL(emm2, ~1, vl);                                                                   \
    y    = __riscv_vfcvt_f_xu_v_f16m##LMUL(emm2, vl);                                                                  \
                                                                                                                       \
    /* get the polynom selection mask              */                                                                  \
    /*     there is one polynom for 0 <= x <= Pi/4 */                                                                  \
    /*     and another one for Pi/4<x<=Pi/2        */                                                                  \
    /*                                             */                                                                  \
    /*     Both branches will be computed.         */                                                                  \
    vbool##MLEN##_t poly_mask = __riscv_vmsne_vx_u16m##LMUL##_b##MLEN(__riscv_vand_vx_u16m##LMUL(emm2, 2, vl), 0, vl); \
                                                                                                                       \
    /* The magic pass: "Extended precision modular arithmetic" */                                                      \
    /*     x = ((x - y * DP1) - y * DP2) - y * DP3;            */                                                      \
    xmm1 = __riscv_vfmul_vf_f16m##LMUL(y, c_minus_cephes_DP1, vl);                                                     \
    xmm2 = __riscv_vfmul_vf_f16m##LMUL(y, c_minus_cephes_DP2, vl);                                                     \
    xmm3 = __riscv_vfmul_vf_f16m##LMUL(y, c_minus_cephes_DP3, vl);                                                     \
    x    = __riscv_vfadd_vv_f16m##LMUL(x, xmm1, vl);                                                                   \
    x    = __riscv_vfadd_vv_f16m##LMUL(x, xmm2, vl);                                                                   \
    x    = __riscv_vfadd_vv_f16m##LMUL(x, xmm3, vl);                                                                   \
                                                                                                                       \
    sign_mask_sin = __riscv_vmxor_mm_b##MLEN(                                                                          \
        sign_mask_sin, __riscv_vmsne_vx_u16m##LMUL##_b##MLEN(__riscv_vand_vx_u16m##LMUL(emm2, 4, vl), 0, vl), vl);     \
    sign_mask_cos = __riscv_vmsne_vx_u16m##LMUL##_b##MLEN(                                                             \
        __riscv_vand_vx_u16m##LMUL(__riscv_vsub_vx_u16m##LMUL(emm2, 2, vl), 4, vl), 0, vl);                            \
                                                                                                                       \
    /* Evaluate the first polynom  (0 <= x <= Pi/4) in y1, */                                                          \
    /*     and the second polynom  (Pi/4 <= x <= 0) in y2  */                                                          \
    vfloat16m##LMUL##_t z = __riscv_vfmul_vv_f16m##LMUL(x, x, vl);                                                     \
    vfloat16m##LMUL##_t y1, y2;                                                                                        \
                                                                                                                       \
    y1 = __riscv_vfmul_vf_f16m##LMUL(z, c_coscof_p0, vl);                                                              \
    y2 = __riscv_vfmul_vf_f16m##LMUL(z, c_sincof_p0, vl);                                                              \
    y1 = __riscv_vfadd_vf_f16m##LMUL(y1, c_coscof_p1, vl);                                                             \
    y2 = __riscv_vfadd_vf_f16m##LMUL(y2, c_sincof_p1, vl);                                                             \
    y1 = __riscv_vfmul_vv_f16m##LMUL(y1, z, vl);                                                                       \
    y2 = __riscv_vfmul_vv_f16m##LMUL(y2, z, vl);                                                                       \
    y1 = __riscv_vfadd_vf_f16m##LMUL(y1, c_coscof_p2, vl);                                                             \
    y2 = __riscv_vfadd_vf_f16m##LMUL(y2, c_sincof_p2, vl);                                                             \
    y1 = __riscv_vfmul_vv_f16m##LMUL(y1, z, vl);                                                                       \
    y2 = __riscv_vfmul_vv_f16m##LMUL(y2, z, vl);                                                                       \
    y1 = __riscv_vfmul_vv_f16m##LMUL(y1, z, vl);                                                                       \
    y2 = __riscv_vfmul_vv_f16m##LMUL(y2, x, vl);                                                                       \
    y1 = __riscv_vfsub_vv_f16m##LMUL(y1, __riscv_vfmul_vf_f16m##LMUL(z, 0.5f, vl), vl);                                \
    y2 = __riscv_vfadd_vv_f16m##LMUL(y2, x, vl);                                                                       \
    y1 = __riscv_vfadd_vf_f16m##LMUL(y1, 1.f, vl);                                                                     \
                                                                                                                       \
    /* select the correct result from the two polynoms */                                                              \
    vfloat16m##LMUL##_t ys = __riscv_vmerge_vvm_f16m##LMUL(y2, y1, poly_mask, vl);                                     \
    vfloat16m##LMUL##_t yc = __riscv_vmerge_vvm_f16m##LMUL(y1, y2, poly_mask, vl);                                     \
    *ysin                  = __riscv_vmerge_vvm_f16m##LMUL(ys, __riscv_vfneg_v_f16m##LMUL(ys, vl), sign_mask_sin, vl); \
    *ycos                  = __riscv_vmerge_vvm_f16m##LMUL(__riscv_vfneg_v_f16m##LMUL(yc, vl), yc, sign_mask_cos, vl); \
  }

_RVV_FLOAT16_SINCOS_OP(1, 16)
_RVV_FLOAT16_SINCOS_OP(2, 8)
_RVV_FLOAT16_SINCOS_OP(4, 4)
_RVV_FLOAT16_SINCOS_OP(8, 2)

#define _RVV_FLOAT16_SIN_OP(LMUL, MLEN)                                                     \
  static inline vfloat16m##LMUL##_t sin_ps_f16m##LMUL(vfloat16m##LMUL##_t x, uint32_t vl) { \
    vfloat16m##LMUL##_t ysin, ycos;                                                         \
    sincos_ps_f16m##LMUL(x, &ysin, &ycos, vl);                                              \
    return ysin;                                                                            \
  }

_RVV_FLOAT16_SIN_OP(1, 16)
_RVV_FLOAT16_SIN_OP(2, 8)
_RVV_FLOAT16_SIN_OP(4, 4)
_RVV_FLOAT16_SIN_OP(8, 2)

#define _RVV_FLOAT16_COS_OP(LMUL, MLEN)                                                     \
  static inline vfloat16m##LMUL##_t cos_ps_f16m##LMUL(vfloat16m##LMUL##_t x, uint32_t vl) { \
    vfloat16m##LMUL##_t ysin, ycos;                                                         \
    sincos_ps_f16m##LMUL(x, &ysin, &ycos, vl);                                              \
    return ycos;                                                                            \
  }

_RVV_FLOAT16_COS_OP(1, 16)
_RVV_FLOAT16_COS_OP(2, 8)
_RVV_FLOAT16_COS_OP(4, 4)
_RVV_FLOAT16_COS_OP(8, 2)

#define c_cephes_HALFMAXLOGF 44.014845935754205f
#define c_cephes_tanh_C1     0.625f

#define c_cephes_tanh_p0 -5.70498872745E-3
#define c_cephes_tanh_p1 +2.06390887954E-2
#define c_cephes_tanh_p2 -5.37397155531E-2
#define c_cephes_tanh_p3 +1.33314422036E-1
#define c_cephes_tanh_p4 -3.33332819422E-1

#define _RVV_FLOAT16_TANH_OP(LMUL, MLEN)                                                                     \
  static inline vfloat16m##LMUL##_t tanh_ps_f16m##LMUL(vfloat16m##LMUL##_t x, uint32_t vl) {                 \
    vfloat16m##LMUL##_t x2 = __riscv_vfsgnj_vf_f16m##LMUL(x, 1.f, vl);                                       \
                                                                                                             \
    vbool##MLEN##_t mask_l  = __riscv_vmfge_vf_f16m##LMUL##_b##MLEN(x2, c_cephes_tanh_C1, vl);               \
    vbool##MLEN##_t mask_l2 = __riscv_vmfgt_vf_f16m##LMUL##_b##MLEN(x2, c_cephes_HALFMAXLOGF, vl);           \
                                                                                                             \
    /* abs(x) >= 0.625 */                                                                                    \
    vfloat16m##LMUL##_t exp_x_x = exp_ps_f16m##LMUL(__riscv_vfadd_vv_f16m##LMUL(x, x, vl), vl);              \
    vfloat16m##LMUL##_t y0      = __riscv_vfrsub_vf_f16m##LMUL(                                              \
        __riscv_vfrdiv_vf_f16m##LMUL(__riscv_vfadd_vf_f16m##LMUL(exp_x_x, 1.f, vl), 2.f, vl), 1.f, vl); \
                                                                                                             \
    /* abs(x) < 0.625                */                                                                      \
    /*   z = x2 * x2;                */                                                                      \
    /*   z =                         */                                                                      \
    /*   (((( -5.70498872745E-3 * z  */                                                                      \
    /*   + 2.06390887954E-2) * z     */                                                                      \
    /*   - 5.37397155531E-2) * z     */                                                                      \
    /*   + 1.33314422036E-1) * z     */                                                                      \
    /*   - 3.33332819422E-1) * z * x */                                                                      \
    /*   + x;                        */                                                                      \
    vfloat16m##LMUL##_t z = __riscv_vfmul_vv_f16m##LMUL(x, x, vl);                                           \
                                                                                                             \
    vfloat16m##LMUL##_t y = __riscv_vfmul_vf_f16m##LMUL(z, c_cephes_tanh_p0, vl);                            \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_tanh_p1, vl);                            \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, z, vl);                                           \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_tanh_p2, vl);                            \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, z, vl);                                           \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_tanh_p3, vl);                            \
    y                     = __riscv_vfmul_vv_f16m##LMUL(y, z, vl);                                           \
    y                     = __riscv_vfadd_vf_f16m##LMUL(y, c_cephes_tanh_p4, vl);                            \
                                                                                                             \
    y = __riscv_vfmul_vv_f16m##LMUL(y, z, vl);                                                               \
    y = __riscv_vfmul_vv_f16m##LMUL(y, x, vl);                                                               \
    y = __riscv_vfadd_vv_f16m##LMUL(y, x, vl);                                                               \
                                                                                                             \
    /* abs(x) > HALFMAXLOGF */                                                                               \
    vfloat16m##LMUL##_t y1 = __riscv_vfsgnj_vv_f16m##LMUL(__riscv_vfmv_v_f_f16m##LMUL(1.f, vl), x, vl);      \
                                                                                                             \
    y = __riscv_vmerge_vvm_f16m##LMUL(y, y0, mask_l, vl);                                                    \
    y = __riscv_vmerge_vvm_f16m##LMUL(y, y1, mask_l2, vl);                                                   \
    return y;                                                                                                \
  }

_RVV_FLOAT16_TANH_OP(1, 16)
_RVV_FLOAT16_TANH_OP(2, 8)
_RVV_FLOAT16_TANH_OP(4, 4)
_RVV_FLOAT16_TANH_OP(8, 2)

#define _RVV_FLOAT16_POW_OP(LMUL, MLEN)                                                                            \
  static inline vfloat16m##LMUL##_t pow_ps_f16m##LMUL(vfloat16m##LMUL##_t a, vfloat16m##LMUL##_t b, uint32_t vl) { \
    /* pow(x, m) = exp(m * log(x)) */                                                                              \
    return exp_ps_f16m##LMUL(__riscv_vfmul_vv_f16m##LMUL(b, log_ps_f16m##LMUL(a, vl), vl), vl);                    \
  }

_RVV_FLOAT16_POW_OP(1, 16)
_RVV_FLOAT16_POW_OP(2, 8)
_RVV_FLOAT16_POW_OP(4, 4)
_RVV_FLOAT16_POW_OP(8, 2)

#define _RVV_FLOAT16_SIGMOID_OP(LMUL, MLEN)                                                                                            \
  static inline vfloat16m##LMUL##_t sigmoid_ps_f16m##LMUL(vfloat16m##LMUL##_t _v, uint32_t vl) {                                       \
    _v                              = __riscv_vfneg_v_f16m##LMUL(_v, vl);                                                              \
    _v                              = exp_ps_f16m##LMUL(_v, vl);                                                                       \
    _v                              = __riscv_vfadd_vf_f16m##LMUL(_v, 1.f, vl);                                                        \
    vfloat16m##LMUL##_t _reciprocal = __riscv_vfrec7_v_f16m##LMUL(_v, vl);                                                             \
    _reciprocal                     = __riscv_vfmul_vv_f16m##LMUL(                                                                     \
        __riscv_vfrsub_vf_f16m##LMUL(__riscv_vfmul_vv_f16m##LMUL(_v, _reciprocal, vl), 2.f, vl), _reciprocal, vl); \
    /* _reciprocal =                                                                                                                   \
     * __riscv_vfmul_vv_f16m##LMUL(__riscv_vfrsub_vf_f16m##LMUL(__riscv_vfmul_vv_f16m##LMUL(_v,                                        \
     * _reciprocal, vl), 2.f, vl), _reciprocal, vl); */                                                                                \
    return _reciprocal;                                                                                                                \
  }

_RVV_FLOAT16_SIGMOID_OP(1, 16)
_RVV_FLOAT16_SIGMOID_OP(2, 8)
_RVV_FLOAT16_SIGMOID_OP(4, 4)
_RVV_FLOAT16_SIGMOID_OP(8, 2)
