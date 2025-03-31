// Description: Tensor conversion kernels
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <conversion.h>
#include <riscv_vector.h>

void tensor_uint8_to_float16(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    *dst++ = (_Float16)*src++;
  }
}

void tensor_uint8_to_float16_rvv(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * w * h * c;
  while (size > 0) {
    uint32_t     vl = __riscv_vsetvl_e8m4(size);
    vuint8m4_t   v  = __riscv_vle8_v_u8m4(src, vl);
    vfloat16m8_t vf = __riscv_vfwcvt_f_xu_v_f16m8(v, vl);
    __riscv_vse16_v_f16m8(dst, vf, vl);
    src  += vl;
    dst  += vl;
    size -= vl;
  }
}

void tensor_float16_to_int8(_Float16 *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    int64_t rounded;
    asm volatile(
        "flh	ft0,0(%[ptr]) \n"
        "fcvt.s.h	ft0,ft0 \n"
        "fcvt.l.s	%[i],ft0,rne"
        : [i] "=r"(rounded)
        : [ptr] "r"(src));
    if (rounded > INT8_MAX) {
      *dst++ = INT8_MAX;
    } else if (rounded < INT8_MIN) {
      *dst++ = INT8_MIN;
    } else {
      *dst++ = (int8_t)rounded;
    }
    src++;

    // This rounds away from zero if there is a tie, but we want
    // to round to even.
    // *dst++ = (int8_t)round(*src++);
  }
}

void tensor_float16_to_int8_rvv(_Float16 *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * w * h * c;
  while (size > 0) {
    uint32_t     vl = __riscv_vsetvl_e16m8(size);
    vfloat16m8_t v  = __riscv_vle16_v_f16m8(src, vl);
    vint8m4_t    vi = __riscv_vfncvt_x_f_w_i8m4(v, vl);
    __riscv_vse8_v_i8m4(dst, vi, vl);
    src  += vl;
    dst  += vl;
    size -= vl;
  }
}

void tensor_uint8_to_float16_scaled(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    *dst++ = (_Float16)(((float)*src++) * IMAGE_DEPTH_SCALE_INV);
  }
}

void tensor_uint8_to_float16_scaled_rvv(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t size = n * w * h * c;
  while (size > 0) {
    uint32_t     vl = __riscv_vsetvl_e8m4(size);
    vuint8m4_t   v  = __riscv_vle8_v_u8m4(src, vl);
    vfloat16m8_t vf = __riscv_vfwcvt_f_xu_v_f16m8(v, vl);
    vf              = __riscv_vfmul_vf_f16m8(vf, IMAGE_DEPTH_SCALE_INV, vl);
    __riscv_vse16_v_f16m8(dst, vf, vl);
    src  += vl;
    dst  += vl;
    size -= vl;
  }
}

void tensor_float16_scaled(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c,
                           _Float16 scale) {
  // Inverse scale factor
  _Float16 scale_inv = (_Float16)(1.0f / (float)scale);

  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    *dst++ = *src++ * scale_inv;
  }
}

void tensor_float16_scaled_rvv(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c,
                               _Float16 scale) {
  // Inverse scale factor
  _Float16 scale_inv = (_Float16)(1.0f / (float)scale);

  uint32_t size = n * w * h * c;
  while (size > 0) {
    uint32_t     vl = __riscv_vsetvl_e16m8(size);
    vfloat16m8_t v  = __riscv_vle16_v_f16m8(src, vl);
    vfloat16m8_t vf = __riscv_vfmul_vf_f16m8(v, scale_inv, vl);
    __riscv_vse16_v_f16m8(dst, vf, vl);
    src  += vl;
    dst  += vl;
    size -= vl;
  }
}

void tensor_format_nchw_to_nhwc_float16(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t  n_size = plane_size * c;
    _Float16 *src_n  = src + ni * n_size;
    _Float16 *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *src_c = src_n + ci * plane_size;
      _Float16 *dst_c = dst_n + ci;
      for (uint32_t px = 0; px < plane_size; px++) {
        *dst_c = *src_c++;
        dst_c  += c;
      }
    }
  }
}

void tensor_format_nchw_to_nhwc_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h,
                                            uint32_t c) {
  uint32_t plane_size = h * w;
  uint32_t bstride    = c * 2;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t  n_size = plane_size * c;
    _Float16 *src_n  = src + ni * n_size;
    _Float16 *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *src_c = src_n + ci * plane_size;
      _Float16 *dst_c = dst_n + ci;
      uint32_t  vl    = __riscv_vsetvl_e16m8(plane_size);
      for (uint32_t x = plane_size; x > 0; x -= vl) {
        vl             = __riscv_vsetvl_e16m8(x);
        vfloat16m8_t v = __riscv_vle16_v_f16m8(src_c, vl);
        __riscv_vsse16_v_f16m8(dst_c, bstride, v, vl);
        src_c += vl;
        dst_c += vl * c;
      }
    }
  }
}

void tensor_format_nhwc_to_nchw_float16(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t  n_size = plane_size * c;
    _Float16 *src_n  = src + ni * n_size;
    _Float16 *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *src_c = src_n + ci;
      _Float16 *dst_c = dst_n + ci * plane_size;
      for (uint32_t px = 0; px < plane_size; px++) {
        *dst_c++ = *src_c;
        src_c    += c;
      }
    }
  }
}

void tensor_format_nhwc_to_nchw_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h,
                                            uint32_t c) {
  uint32_t plane_size = h * w;
  uint32_t bstride    = c * 2;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t  n_size = plane_size * c;
    _Float16 *src_n  = src + ni * n_size;
    _Float16 *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      _Float16 *src_c = src_n + ci;
      _Float16 *dst_c = dst_n + ci * plane_size;
      uint32_t  vl    = __riscv_vsetvl_e16m8(plane_size);
      for (uint32_t x = plane_size; x > 0; x -= vl) {
        vl             = __riscv_vsetvl_e16m8(x);
        vfloat16m8_t v = __riscv_vlse16_v_f16m8(src_c, bstride, vl);
        __riscv_vse16_v_f16m8(dst_c, v, vl);
        src_c += vl * c;
        dst_c += vl;
      }
    }
  }
}

void tensor_format_nchw_to_nhwc_int8(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    int8_t  *src_n  = src + ni * n_size;
    int8_t  *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      int8_t *src_c = src_n + ci * plane_size;
      int8_t *dst_c = dst_n + ci;
      for (uint32_t px = 0; px < plane_size; px++) {
        *dst_c = *src_c++;
        dst_c  += c;
      }
    }
  }
}

void tensor_format_nchw_to_nhwc_int8_rvv(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  uint32_t bstride    = c;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    int8_t  *src_n  = src + ni * n_size;
    int8_t  *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      int8_t  *src_c = src_n + ci * plane_size;
      int8_t  *dst_c = dst_n + ci;
      uint32_t vl    = __riscv_vsetvl_e8m8(plane_size);
      for (uint32_t x = plane_size; x > 0; x -= vl) {
        vl          = __riscv_vsetvl_e8m8(x);
        vint8m8_t v = __riscv_vle8_v_i8m8(src_c, vl);
        __riscv_vsse8_v_i8m8(dst_c, bstride, v, vl);
        src_c += vl;
        dst_c += vl * c;
      }
    }
  }
}

void tensor_format_nhwc_to_nchw_int8(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    int8_t  *src_n  = src + ni * n_size;
    int8_t  *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      int8_t *src_c = src_n + ci;
      int8_t *dst_c = dst_n + ci * plane_size;
      for (uint32_t px = 0; px < plane_size; px++) {
        *dst_c++ = *src_c;
        src_c    += c;
      }
    }
  }
}

void tensor_format_nhwc_to_nchw_int8_rvv(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  uint32_t bstride    = c;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    int8_t  *src_n  = src + ni * n_size;
    int8_t  *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      int8_t  *src_c = src_n + ci;
      int8_t  *dst_c = dst_n + ci * plane_size;
      uint32_t vl    = __riscv_vsetvl_e16m8(plane_size);
      for (uint32_t x = plane_size; x > 0; x -= vl) {
        vl          = __riscv_vsetvl_e8m8(x);
        vint8m8_t v = __riscv_vlse8_v_i8m8(src_c, bstride, vl);
        __riscv_vse8_v_i8m8(dst_c, v, vl);
        src_c += vl * c;
        dst_c += vl;
      }
    }
  }
}

void tensor_format_nchw_to_nhwc_uint8(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    uint8_t *src_n  = src + ni * n_size;
    uint8_t *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      uint8_t *src_c = src_n + ci * plane_size;
      uint8_t *dst_c = dst_n + ci;
      for (uint32_t px = 0; px < plane_size; px++) {
        *dst_c = *src_c++;
        dst_c  += c;
      }
    }
  }
}

void tensor_format_nchw_to_nhwc_uint8_rvv(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  uint32_t bstride    = c;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    uint8_t *src_n  = src + ni * n_size;
    uint8_t *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      uint8_t *src_c = src_n + ci * plane_size;
      uint8_t *dst_c = dst_n + ci;
      uint32_t vl    = __riscv_vsetvl_e8m8(plane_size);
      for (uint32_t x = plane_size; x > 0; x -= vl) {
        vl           = __riscv_vsetvl_e8m8(x);
        vuint8m8_t v = __riscv_vle8_v_u8m8(src_c, vl);
        __riscv_vsse8_v_u8m8(dst_c, bstride, v, vl);
        src_c += vl;
        dst_c += vl * c;
      }
    }
  }
}

void tensor_format_nhwc_to_nchw_uint8(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    uint8_t *src_n  = src + ni * n_size;
    uint8_t *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      uint8_t *src_c = src_n + ci;
      uint8_t *dst_c = dst_n + ci * plane_size;
      for (uint32_t px = 0; px < plane_size; px++) {
        *dst_c++ = *src_c;
        src_c    += c;
      }
    }
  }
}

void tensor_format_nhwc_to_nchw_uint8_rvv(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c) {
  uint32_t plane_size = h * w;
  uint32_t bstride    = c;
  for (uint32_t ni = 0; ni < n; ni++) {
    uint32_t n_size = plane_size * c;
    uint8_t *src_n  = src + ni * n_size;
    uint8_t *dst_n  = dst + ni * n_size;

    for (uint32_t ci = 0; ci < c; ci++) {
      uint8_t *src_c = src_n + ci;
      uint8_t *dst_c = dst_n + ci * plane_size;
      uint32_t vl    = __riscv_vsetvl_e16m8(plane_size);
      for (uint32_t x = plane_size; x > 0; x -= vl) {
        vl           = __riscv_vsetvl_e8m8(x);
        vuint8m8_t v = __riscv_vlse8_v_u8m8(src_c, bstride, vl);
        __riscv_vse8_v_u8m8(dst_c, v, vl);
        src_c += vl * c;
        dst_c += vl;
      }
    }
  }
}
