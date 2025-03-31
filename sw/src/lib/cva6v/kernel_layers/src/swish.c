// Description: Swish kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <swish.h>
#include <math.h>
#include <riscv_vector.h>
#include <rvv_math.h>

void swish(_Float16 *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    matrix[i] = (float)matrix[i] / (1.0f + expf(-(float)matrix[i]));
  }
}

void swish_rvv(_Float16 *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * h * w * c;
  while (size > 0) {
    uint32_t     vl  = __riscv_vsetvl_e16m4(size);
    vfloat16m4_t v   = __riscv_vle16_v_f16m4(matrix, vl);
    vfloat16m4_t vn  = __riscv_vfneg_v_f16m4(v, vl);
    vfloat16m4_t d   = __riscv_vfadd_vf_f16m4(exp_ps_f16m4(vn, vl), 1.0f, vl);
    vfloat16m4_t rec = __riscv_vfrec7_v_f16m4(d, vl);
    vfloat16m4_t r   = __riscv_vfmul_vv_f16m4(v, rec, vl);
    __riscv_vse16_v_f16m4(matrix, r, vl);
    matrix += vl;
    size   -= vl;
  }
}
