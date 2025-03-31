// Description: RISC-V vector operations header
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <riscv_vector.h>
#include <scalar_ops.h>
#include <stdint.h>

/// Vector float reduction sum operation (unordered).
/// Has a runtime of log2(vl).
///
/// @param[in] vs2 vector to sum up
/// @param[in] vl  vector length
/// @return Sum of all elements in input vector vs2
#define _RVV_VFREDUSUM(SEW, LMUL)                                                                               \
  static inline vfloat##SEW##m##LMUL##_t vfredusum_f##SEW##m##LMUL(vfloat##SEW##m##LMUL##_t vs2, uint32_t vl) { \
    /* Round vl to be of power of 2 */                                                                          \
    uint32_t                 vl_  = CEIL_POW2(vl) / 2;                                                          \
    /* On first iteration only add overlapping values (happens with under-filled vectors) */                    \
    vfloat##SEW##m##LMUL##_t vsld = __riscv_vslidedown_vx_f##SEW##m##LMUL(vs2, vl_, vl - vl_);                  \
    vfloat##SEW##m##LMUL##_t vsum = __riscv_vfadd_vv_f##SEW##m##LMUL##_tu(vs2, vs2, vsld, vl - vl_);            \
    /* Slide and add (log(n) runtime)*/                                                                         \
    while (vl_ > 1) {                                                                                           \
      vl_  = vl_ / 2;                                                                                           \
      vsld = __riscv_vslidedown_vx_f##SEW##m##LMUL(vsum, vl_, vl_);                                             \
      vsum = __riscv_vfadd_vv_f##SEW##m##LMUL(vsum, vsld, vl_);                                                 \
    }                                                                                                           \
    return vsum;                                                                                                \
  }

_RVV_VFREDUSUM(16, 1)
_RVV_VFREDUSUM(16, 2)
_RVV_VFREDUSUM(16, 4)
_RVV_VFREDUSUM(16, 8)
_RVV_VFREDUSUM(32, 1)
_RVV_VFREDUSUM(32, 2)
_RVV_VFREDUSUM(32, 4)
_RVV_VFREDUSUM(32, 8)

/// Vector integer reduction sum operation.
/// Has a runtime of log2(vl).
///
/// @param[in] vs2 vector to sum up
/// @param[in] vl  vector length
/// @return Sum of all elements in input vector vs2
#define _RVV_VREDSUM(TYPE, CONF)                                                             \
  static inline TYPE vredsum_##CONF(TYPE vs2, uint32_t vl) {                                 \
    /* Round vl to be of power of 2 */                                                       \
    uint32_t vl_  = CEIL_POW2(vl) / 2;                                                       \
    /* On first iteration only add overlapping values (happens with under-filled vectors) */ \
    /* Note that tail-undisturbed is used for the add to preserve non-overlapping values */  \
    TYPE     vsld = __riscv_vslidedown_vx_##CONF(vs2, vl_, vl - vl_);                        \
    TYPE     vsum = __riscv_vadd_vv_##CONF##_tu(vs2, vs2, vsld, vl - vl_);                   \
    /* Slide and add (log(n) runtime)*/                                                      \
    while (vl_ > 1) {                                                                        \
      vl_  = vl_ / 2;                                                                        \
      vsld = __riscv_vslidedown_vx_##CONF(vsum, vl_, vl_);                                   \
      vsum = __riscv_vadd_vv_##CONF(vsum, vsld, vl_);                                        \
    }                                                                                        \
    return vsum;                                                                             \
  }

#define _RVV_VREDSUM_IU(SEW, LMUL)                      \
  _RVV_VREDSUM(vint##SEW##m##LMUL##_t, i##SEW##m##LMUL) \
  _RVV_VREDSUM(vuint##SEW##m##LMUL##_t, u##SEW##m##LMUL)

_RVV_VREDSUM_IU(8, 1)
_RVV_VREDSUM_IU(8, 2)
_RVV_VREDSUM_IU(8, 4)
_RVV_VREDSUM_IU(8, 8)
_RVV_VREDSUM_IU(16, 1)
_RVV_VREDSUM_IU(16, 2)
_RVV_VREDSUM_IU(16, 4)
_RVV_VREDSUM_IU(16, 8)
_RVV_VREDSUM_IU(32, 1)
_RVV_VREDSUM_IU(32, 2)
_RVV_VREDSUM_IU(32, 4)
_RVV_VREDSUM_IU(32, 8)

static inline void* vmemcpy(void* restrict dst, const void* restrict src, size_t num_bytes) {
  size_t remaining = num_bytes;
  void*  dst_copy  = dst;
  while (remaining > 0) {
    size_t     vl        = __riscv_vsetvl_e8m8(remaining);
    vuint8m8_t mem_chunk = __riscv_vle8_v_u8m8(src, vl);
    __riscv_vse8_v_u8m8(dst, mem_chunk, vl);
    dst       += vl;
    src       += vl;
    remaining -= vl;
  }
  return dst_copy;
}

static inline void* vmemset(void* restrict ptr, int value, size_t num_bytes) {
  size_t remaining = num_bytes;
  void*  ptr_copy  = ptr;
  while (remaining > 0) {
    size_t     vl        = __riscv_vsetvl_e8m8(remaining);
    vuint8m8_t mem_chunk = __riscv_vmv_v_x_u8m8((uint8_t)value, vl);
    __riscv_vse8_v_u8m8(ptr, mem_chunk, vl);
    ptr       += vl;
    remaining -= vl;
  }
  return ptr_copy;
}
