// Description: Softmax kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <softmax.h>
#include <math.h>
#include <riscv_vector.h>
#include <rvv_math.h>
#include <rvv_ops.h>

void softmax(_Float16 *matrix, uint32_t w, uint32_t h, uint32_t dim) {
  if (dim == X_DIMENSION) {
    softmax_xdim(matrix, w, h);
  } else if (dim == Y_DIMENSION) {
    softmax_ydim(matrix, w, h);
  }
}

void softmax_xdim(_Float16 *matrix, uint32_t w, uint32_t h) {
  _Float16 *matrix_ptr = matrix;
  for (uint32_t hi = 0; hi < h; hi++) {
    _Float16 sum = 0.0f;
    for (uint32_t wi = 0; wi < w; wi++) {
      _Float16 _exp  = expf((float)matrix_ptr[wi]);
      sum            += _exp;
      matrix_ptr[wi] = _exp;
    }

    _Float16 sum_inv = 1.0f / (float)sum;
    for (uint32_t wi = 0; wi < w; wi++) {
      matrix_ptr[wi] = matrix_ptr[wi] * sum_inv;
    }

    matrix_ptr += h;
  }
}

void softmax_ydim(_Float16 *matrix, uint32_t w, uint32_t h) {
  for (uint32_t wi = 0; wi < w; wi++) {
    _Float16 *matrix_ptr = matrix + wi;
    _Float16  sum        = 0.0f;
    for (uint32_t hi = 0; hi < h; hi++) {
      uint32_t idx    = hi * w;
      _Float16 _exp   = expf((float)matrix_ptr[idx]);
      sum             += _exp;
      matrix_ptr[idx] = _exp;
    }

    _Float16 sum_inv = 1.0f / (float)sum;
    for (uint32_t hi = 0; hi < h; hi++) {
      uint32_t idx    = hi * w;
      matrix_ptr[idx] = matrix_ptr[idx] * sum_inv;
    }
  }
}

void softmax_xdim_rvv(_Float16 *matrix, uint32_t w, uint32_t h) {
  _Float16 *matrix_ptr = matrix;
  for (uint32_t hi = 0; hi < h; hi++) {
    _Float16 *_matrix_ptr = matrix_ptr;

    uint32_t     size     = w;
    uint32_t     vl_first = __riscv_vsetvl_e16m2(size);
    vfloat16m2_t vacc     = __riscv_vfmv_v_f_f16m2(0.0f, vl_first);
    while (size > 0) {
      uint32_t vl = __riscv_vsetvl_e16m2(size);

      vfloat16m2_t v   = __riscv_vle16_v_f16m2(_matrix_ptr, vl);
      vfloat16m2_t exp = exp_ps_f16m2(v, vl);
      __riscv_vse16_v_f16m2(_matrix_ptr, exp, vl);
      vacc = __riscv_vfadd_vv_f16m2(vacc, exp, vl);

      size        -= vl;
      _matrix_ptr += vl;
    }
    vfloat16m2_t vsum = vfredusum_f16m2(vacc, vl_first);

    _Float16 sum;
    __riscv_vse16_v_f16m2(&sum, vsum, 1);
    _Float16 sum_inv = 1.0f / (float)sum;

    _matrix_ptr = matrix_ptr;
    size        = w;
    while (size > 0) {
      uint32_t vl = __riscv_vsetvl_e16m2(size);

      vfloat16m2_t v = __riscv_vle16_v_f16m2(_matrix_ptr, vl);
      vfloat16m2_t r = __riscv_vfmul_vf_f16m2(v, sum_inv, vl);
      __riscv_vse16_v_f16m2(_matrix_ptr, r, vl);

      size        -= vl;
      _matrix_ptr += vl;
    }

    matrix_ptr += h;
  }
}

void softmax_ydim_rvv(_Float16 *matrix, uint32_t w, uint32_t h) {
  _Float16 *matrix_ptr = matrix;
  uint32_t  x_size     = w;
  while (x_size > 0) {
    uint32_t  vl          = __riscv_vsetvl_e16m4(x_size);
    _Float16 *_matrix_ptr = matrix_ptr;

    vfloat16m4_t vacc = __riscv_vfmv_v_f_f16m4(0.0f, vl);
    for (uint32_t hi = 0; hi < h; hi++) {
      vfloat16m4_t v   = __riscv_vle16_v_f16m4(_matrix_ptr, vl);
      vfloat16m4_t exp = exp_ps_f16m4(v, vl);
      __riscv_vse16_v_f16m4(_matrix_ptr, exp, vl);
      vacc = __riscv_vfadd_vv_f16m4(vacc, exp, vl);

      _matrix_ptr += w;
    }

    vfloat16m4_t vsum_inv = __riscv_vfrec7_v_f16m4(vacc, vl);

    _matrix_ptr = matrix_ptr;
    for (uint32_t hi = 0; hi < h; hi++) {
      vfloat16m4_t v = __riscv_vle16_v_f16m4(_matrix_ptr, vl);
      vfloat16m4_t r = __riscv_vfmul_vv_f16m4(v, vsum_inv, vl);
      __riscv_vse16_v_f16m4(_matrix_ptr, r, vl);

      _matrix_ptr += w;
    }

    x_size     -= vl;
    matrix_ptr += vl;
  }
}

void softmax_rvv(_Float16 *matrix, uint32_t w, uint32_t h, uint32_t dim) {
  if (dim == X_DIMENSION) {
    softmax_xdim_rvv(matrix, w, h);
  } else if (dim == Y_DIMENSION) {
    softmax_ydim_rvv(matrix, w, h);
  }
}
