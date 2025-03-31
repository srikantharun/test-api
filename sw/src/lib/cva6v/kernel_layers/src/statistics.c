// Description: Statistics kernels
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <statistics.h>
#include <math.h>
#include <riscv_vector.h>
#include <rvv_math.h>
#include <rvv_ops.h>

void mean(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, uint32_t format) {
  uint32_t cplane = h * w;

  if (format == NORM_BATCH) {
    uint32_t nplane = n * cplane;
    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *tensor_cptr = tensor + ci * cplane;
      float     sum         = 0.0f;
      for (uint32_t ni = 0; ni < n; ni++) {
        _Float16 *tensor_nptr = tensor_cptr + ni * c * cplane;
        for (uint32_t e = 0; e < cplane; e++) {
          sum += (float)tensor_nptr[e];
        }
      }
      mean[ci] = (_Float16)(sum / nplane);
    }
  }

  if (format == NORM_LAYER) {
    uint32_t  nplane     = c * cplane;
    _Float16 *tensor_ptr = tensor;
    for (uint32_t ni = 0; ni < n; ni++) {
      float sum = 0.0f;
      for (uint32_t e = 0; e < nplane; e++) {
        sum += (float)tensor_ptr[e];
      }
      mean[ni]   = (_Float16)(sum / nplane);
      tensor_ptr += nplane;
    }
  }

  if (format == NORM_INSTANCE) {
    // uint32_t  nplane     = c * cplane;
    _Float16 *tensor_ptr = tensor;
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 *mean_ptr = mean + ni * c;
      for (uint32_t ci = 0; ci < c; ci++) {
        float sum = 0.0f;
        for (uint32_t e = 0; e < cplane; e++) {
          sum += (float)tensor_ptr[e];
        }
        mean_ptr[ci] = (_Float16)(sum / cplane);
        tensor_ptr   += cplane;
      }
    }
  }
}

void mean_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, uint32_t format) {
  uint32_t cplane = h * w;

  if (format == NORM_BATCH) {
    uint32_t nplane = n * cplane;
    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16    *tensor_cptr = tensor + ci * cplane;
      uint32_t     vl_first    = __riscv_vsetvl_e32m8(cplane);
      vfloat32m8_t vacc        = __riscv_vfmv_v_f_f32m8(0.0f, vl_first);
      for (uint32_t ni = 0; ni < n; ni++) {
        _Float16 *tensor_nptr = tensor_cptr + ni * c * cplane;

        uint32_t size = cplane;
        while (size > 0) {
          uint32_t     vl = __riscv_vsetvl_e16m4(size);
          vfloat16m4_t v  = __riscv_vle16_v_f16m4(tensor_nptr, vl);
          vacc            = __riscv_vfwadd_wv_f32m8(vacc, v, vl);

          tensor_nptr += vl;
          size        -= vl;
        }
      }
      vfloat32m8_t vsum = vfredusum_f32m8(vacc, vl_first);

      float sum;
      __riscv_vse32_v_f32m8(&sum, vsum, 1);
      mean[ci] = (_Float16)(sum / nplane);
    }
  }

  if (format == NORM_LAYER) {
    uint32_t  nplane     = c * cplane;
    _Float16 *tensor_ptr = tensor;
    for (uint32_t ni = 0; ni < n; ni++) {
      uint32_t     size     = nplane;
      uint32_t     vl_first = __riscv_vsetvl_e32m8(size);
      vfloat32m8_t vacc     = __riscv_vfmv_v_f_f32m8(0.0f, vl_first);
      while (size > 0) {
        uint32_t     vl = __riscv_vsetvl_e16m4(size);
        vfloat16m4_t v  = __riscv_vle16_v_f16m4(tensor_ptr, vl);
        vacc            = __riscv_vfwadd_wv_f32m8(vacc, v, vl);

        tensor_ptr += vl;
        size       -= vl;
      }
      vfloat32m8_t vsum = vfredusum_f32m8(vacc, vl_first);

      float sum;
      __riscv_vse32_v_f32m8(&sum, vsum, 1);
      mean[ni] = (_Float16)(sum / nplane);
    }
  }

  if (format == NORM_INSTANCE) {
    uint32_t nplane = c * cplane;
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 *tensor_nptr = tensor + ni * nplane;
      _Float16 *mean_ptr    = mean + ni * c;
      for (uint32_t ci = 0; ci < c; ci++) {
        _Float16    *tensor_cptr = tensor_nptr + ci * cplane;
        uint32_t     size        = cplane;
        uint32_t     vl_first    = __riscv_vsetvl_e32m8(size);
        vfloat32m8_t vacc        = __riscv_vfmv_v_f_f32m8(0.0f, vl_first);
        ;
        while (size > 0) {
          uint32_t     vl = __riscv_vsetvl_e16m4(size);
          vfloat16m4_t v  = __riscv_vle16_v_f16m4(tensor_cptr, vl);
          vacc            = __riscv_vfwadd_wv_f32m8(vacc, v, vl);

          tensor_cptr += vl;
          size        -= vl;
        }
        vfloat32m8_t vsum = vfredusum_f32m8(vacc, vl_first);

        float sum;
        __riscv_vse32_v_f32m8(&sum, vsum, 1);
        mean_ptr[ci] = (_Float16)(sum / cplane);
      }
    }
  }
}

void std(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std,
         uint32_t format) {
  uint32_t cplane = h * w;

  if (format == NORM_BATCH) {
    uint32_t nplane = n * cplane;
    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *tensor_ptr = tensor + ci * cplane;
      _Float16  mean_      = mean[ci];
      float     sum        = 0.0f;
      for (uint32_t ni = 0; ni < n; ni++) {
        for (uint32_t e = 0; e < cplane; e++) {
          _Float16 div = tensor_ptr[e] - mean_;
          float    dev = (float)div * (float)div;
          sum          += dev;
        }
        tensor_ptr += c * cplane;
      }
      std[ci] = (_Float16)sqrtf(sum / nplane + EPSYLON);
    }
  }

  if (format == NORM_LAYER) {
    uint32_t  nplane     = c * cplane;
    _Float16 *tensor_ptr = tensor;
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 mean_ = mean[ni];
      float    sum   = 0.0f;
      for (uint32_t e = 0; e < nplane; e++) {
        _Float16 div = tensor_ptr[e] - mean_;
        float    dev = (float)div * (float)div;
        sum          += dev;
      }
      std[ni]    = (_Float16)sqrtf(sum / nplane + EPSYLON);
      tensor_ptr += nplane;
    }
  }

  if (format == NORM_INSTANCE) {
    _Float16 *tensor_ptr = tensor;
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 *mean_ptr = mean + ni * c;
      _Float16 *std_ptr  = std + ni * c;
      for (uint32_t ci = 0; ci < c; ci++) {
        _Float16 mean_ = mean_ptr[ci];
        float    sum   = 0.0f;
        for (uint32_t e = 0; e < cplane; e++) {
          _Float16 div = tensor_ptr[e] - mean_;
          float    dev = (float)div * (float)div;
          sum          += dev;
        }
        std_ptr[ci] = (_Float16)sqrtf(sum / cplane + EPSYLON);
        tensor_ptr  += cplane;
      }
    }
  }
}

void std_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std,
             uint32_t format) {
  uint32_t cplane = h * w;

  if (format == NORM_BATCH) {
    uint32_t nplane = c * cplane;
    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16    *tensor_cptr = tensor + ci * cplane;
      _Float16     mean_       = mean[ci];
      uint32_t     vl_first    = __riscv_vsetvl_e16m2(cplane);
      vfloat32m2_t vacc        = __riscv_vfmv_v_f_f32m2(0.0f, vl_first);
      for (uint32_t ni = 0; ni < n; ni++) {
        _Float16 *tensor_nptr = tensor_cptr + ni * nplane;

        uint32_t size = cplane;
        while (size > 0) {
          uint32_t     vl = __riscv_vsetvl_e16m1(size);
          vfloat16m1_t v  = __riscv_vle16_v_f16m1(tensor_nptr, vl);
          v               = __riscv_vfsub_vf_f16m1(v, mean_, vl);
          vacc            = __riscv_vfwmacc_vv_f32m2(vacc, v, v, vl);

          tensor_nptr += vl;
          size        -= vl;
        }
      }
      vfloat32m2_t vsum = vfredusum_f32m2(vacc, vl_first);

      float sum;
      __riscv_vse32_v_f32m2(&sum, vsum, 1);
      std[ci] = (_Float16)sqrtf(sum / (n * cplane) + EPSYLON);
    }
  }

  if (format == NORM_LAYER) {
    uint32_t  nplane     = c * cplane;
    _Float16 *tensor_ptr = tensor;
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 mean_ = mean[ni];

      uint32_t     size     = nplane;
      uint32_t     vl_first = __riscv_vsetvl_e32m2(size);
      vfloat32m2_t vacc     = __riscv_vfmv_v_f_f32m2(0.0f, vl_first);
      while (size > 0) {
        uint32_t     vl = __riscv_vsetvl_e16m1(size);
        vfloat16m1_t v  = __riscv_vle16_v_f16m1(tensor_ptr, vl);
        v               = __riscv_vfsub_vf_f16m1(v, mean_, vl);
        vacc            = __riscv_vfwmacc_vv_f32m2(vacc, v, v, vl);

        tensor_ptr += vl;
        size       -= vl;
      }
      vfloat32m2_t vsum = vfredusum_f32m2(vacc, vl_first);

      float sum;
      __riscv_vse32_v_f32m2(&sum, vsum, 1);
      std[ni] = (_Float16)sqrtf(sum / nplane + EPSYLON);
    }
  }

  if (format == NORM_INSTANCE) {
    uint32_t nplane = c * cplane;
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 *tensor_nptr = tensor + ni * nplane;
      _Float16 *mean_ptr    = mean + ni * c;
      _Float16 *std_ptr     = std + ni * c;
      for (uint32_t ci = 0; ci < c; ci++) {
        _Float16 *tensor_cptr = tensor_nptr + ci * cplane;
        _Float16  mean_       = mean_ptr[ci];

        uint32_t     size     = cplane;
        uint32_t     vl_first = __riscv_vsetvl_e32m2(size);
        vfloat32m2_t vacc     = __riscv_vfmv_v_f_f32m2(0.0f, vl_first);
        while (size > 0) {
          uint32_t     vl = __riscv_vsetvl_e16m1(size);
          vfloat16m1_t v  = __riscv_vle16_v_f16m1(tensor_cptr, vl);
          v               = __riscv_vfsub_vf_f16m1(v, mean_, vl);
          vacc            = __riscv_vfwmacc_vv_f32m2(vacc, v, v, vl);

          tensor_cptr += vl;
          size        -= vl;
        }
        vfloat32m2_t vsum = vfredusum_f32m2(vacc, vl_first);

        float sum;
        __riscv_vse32_v_f32m2(&sum, vsum, 1);
        std_ptr[ci] = (_Float16)sqrtf(sum / cplane + EPSYLON);
      }
    }
  }
}

void batch_norm(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std) {
  uint32_t cplane = h * w;
  uint32_t nplane = c * cplane;
  for (uint32_t ci = 0; ci < c; ci++) {
    _Float16 *tensor_ptr = tensor + ci * cplane;
    _Float16  mean_      = mean[ci];
    _Float16  std_inv    = (_Float16)(1.0f / (float)std[ci]);
    for (uint32_t ni = 0; ni < n; ni++) {
      for (uint32_t e = 0; e < cplane; e++) {
        tensor_ptr[e] = (tensor_ptr[e] - mean_) * std_inv;
      }
      tensor_ptr += nplane;
    }
  }
}

void batch_norm_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std) {
  uint32_t cplane = h * w;
  uint32_t nplane = c * cplane;
  for (uint32_t ci = 0; ci < c; ci++) {
    _Float16 *tensor_cptr = tensor + ci * cplane;
    _Float16  mean_       = mean[ci];
    _Float16  std_inv     = (_Float16)(1.0f / (float)std[ci]);
    for (uint32_t ni = 0; ni < n; ni++) {
      _Float16 *tensor_nptr = tensor_cptr + ni * nplane;

      uint32_t size = cplane;
      while (size > 0) {
        uint32_t     vl = __riscv_vsetvl_e16m8(size);
        vfloat16m8_t v  = __riscv_vle16_v_f16m8(tensor_nptr, vl);
        v               = __riscv_vfsub_vf_f16m8(v, mean_, vl);
        v               = __riscv_vfmul_vf_f16m8(v, std_inv, vl);
        __riscv_vse16_v_f16m8(tensor_nptr, v, vl);

        tensor_nptr += vl;
        size        -= vl;
      }
    }
  }
}

void layer_norm(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std) {
  uint32_t  cplane     = h * w;
  uint32_t  nplane     = c * cplane;
  _Float16 *tensor_ptr = tensor;
  for (uint32_t ni = 0; ni < n; ni++) {
    _Float16 mean_   = mean[ni];
    _Float16 std_inv = (_Float16)(1.0f / (float)std[ni]);
    for (uint32_t e = 0; e < nplane; e++) {
      tensor_ptr[e] = (tensor_ptr[e] - mean_) * std_inv;
    }
    tensor_ptr += nplane;
  }
}

void layer_norm_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std) {
  uint32_t cplane = h * w;
  uint32_t nplane = c * cplane;
  for (uint32_t ni = 0; ni < n; ni++) {
    _Float16 *tensor_nptr = tensor + ni * nplane;
    _Float16  mean_       = mean[ni];
    _Float16  std_inv     = (_Float16)(1.0f / (float)std[ni]);

    uint32_t size = nplane;
    while (size > 0) {
      uint32_t     vl = __riscv_vsetvl_e16m8(size);
      vfloat16m8_t v  = __riscv_vle16_v_f16m8(tensor_nptr, vl);
      v               = __riscv_vfsub_vf_f16m8(v, mean_, vl);
      v               = __riscv_vfmul_vf_f16m8(v, std_inv, vl);
      __riscv_vse16_v_f16m8(tensor_nptr, v, vl);

      tensor_nptr += vl;
      size        -= vl;
    }
  }
}

void instance_norm(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std) {
  uint32_t cplane = h * w;
  uint32_t nplane = c * cplane;
  for (uint32_t ni = 0; ni < n; ni++) {
    _Float16 *tensor_nptr = tensor + ni * nplane;
    _Float16 *mean_ptr    = mean + ni * c;
    _Float16 *std_ptr     = std + ni * c;
    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *tensor_cptr = tensor_nptr + ci * cplane;
      _Float16  mean_       = mean_ptr[ci];
      _Float16  std_inv     = (_Float16)(1.0f / (float)std_ptr[ci]);
      for (uint32_t e = 0; e < cplane; e++) {
        tensor_cptr[e] = (tensor_cptr[e] - mean_) * std_inv;
      }
    }
  }
}

void instance_norm_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean,
                       _Float16 *std) {
  uint32_t cplane = h * w;
  uint32_t nplane = c * cplane;
  for (uint32_t ni = 0; ni < n; ni++) {
    _Float16 *tensor_nptr = tensor + ni * nplane;
    _Float16 *mean_ptr    = mean + ni * c;
    _Float16 *std_ptr     = std + ni * c;
    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *tensor_cptr = tensor_nptr + ci * cplane;
      _Float16  mean_       = mean_ptr[ci];
      _Float16  std_inv     = (_Float16)(1.0f / (float)std_ptr[ci]);

      uint32_t size = cplane;
      while (size > 0) {
        uint32_t     vl = __riscv_vsetvl_e16m8(size);
        vfloat16m8_t v  = __riscv_vle16_v_f16m8(tensor_cptr, vl);
        v               = __riscv_vfsub_vf_f16m8(v, mean_, vl);
        v               = __riscv_vfmul_vf_f16m8(v, std_inv, vl);
        __riscv_vse16_v_f16m8(tensor_cptr, v, vl);

        tensor_cptr += vl;
        size        -= vl;
      }
    }
  }
}
