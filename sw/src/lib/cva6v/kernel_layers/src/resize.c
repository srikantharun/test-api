// Description: Resize kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <resize.h>
#include <riscv_vector.h>
#include <tensor_op.h>

#define MAX(x, y) (x < y ? y : x)
#define MIN(x, y) (x < y ? x : y)

int resize_float16(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst, uint32_t h_dst,
                   uint32_t c_cnt, uint32_t tensor_format, enum interpolation_mode interpolation) {
  switch (interpolation) {
    case BILINEAR:
      bilinear_interpolation_float16(src, dst, w_src, h_src, w_dst, h_dst, c_cnt, tensor_format);
      break;
    default:
      return -1;
  }

  return 0;
}

void bilinear_interpolation_float16(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst,
                                    uint32_t h_dst, uint32_t c_cnt, uint32_t format) {
  // Height and width scaling factor
  _Float16 x_scale_factor = (_Float16)w_src / (_Float16)w_dst;
  _Float16 y_scale_factor = (_Float16)h_src / (_Float16)h_dst;

  for (uint32_t c = 0; c < c_cnt; c++) {
    for (uint32_t y = 0; y < h_dst; y++) {
      // Calculate point to interpolate on y-axis of input image
      _Float16 yp     = MAX((y + 0.5f) * (float)y_scale_factor - 0.5f, 0.0f);
      // Y-grid surrounding interpolation point
      uint32_t y1     = (uint32_t)yp;
      uint32_t y2     = MIN(y1 + 1, h_src - 1);
      // Distances of yp to y-grid
      _Float16 y1_div = yp - (_Float16)y1;
      _Float16 y2_div = (_Float16)1.0f - y1_div;

      for (uint32_t x = 0; x < w_dst; x++) {
        // Calculate point to interpolate on x-axis of input image
        _Float16 xp     = MAX((x + 0.5f) * (float)x_scale_factor - 0.5f, 0.0f);
        // X-grid surrounding interpolation point
        int32_t  x1     = (int32_t)xp;
        int32_t  x2     = MIN((uint32_t)x1 + 1, w_src - 1);
        // Distance of xp to x-grid
        _Float16 x1_div = xp - (_Float16)x1;
        _Float16 x2_div = (_Float16)1.0f - x1_div;

        // Calculate load addrs
        uint32_t q11_addr, q21_addr, q12_addr, q22_addr;
        if (format == TENSOR_FORMAT_NCHW) {
          q11_addr = c * h_src * w_src + y1 * w_src + x1;
          q21_addr = c * h_src * w_src + y1 * w_src + x2;
          q12_addr = c * h_src * w_src + y2 * w_src + x1;
          q22_addr = c * h_src * w_src + y2 * w_src + x2;
        } else {
          q11_addr = y1 * w_src * c_cnt + x1 * c_cnt + c;
          q21_addr = y1 * w_src * c_cnt + x2 * c_cnt + c;
          q12_addr = y2 * w_src * c_cnt + x1 * c_cnt + c;
          q22_addr = y2 * w_src * c_cnt + x2 * c_cnt + c;
        }

        // Get pixel values surrounding xp and yp
        _Float16 q11 = src[q11_addr];
        _Float16 q21 = src[q21_addr];
        _Float16 q12 = src[q12_addr];
        _Float16 q22 = src[q22_addr];

        // Calculate bilinear interpolation
        _Float16 r1 = q11 * x2_div + q21 * x1_div;
        _Float16 r2 = q12 * x2_div + q22 * x1_div;
        _Float16 p  = r1 * y2_div + r2 * y1_div;

        // Store result
        if (format == TENSOR_FORMAT_NCHW) {
          *dst++ = p;
        } else {
          dst[y * w_dst * c_cnt + x * c_cnt + c] = p;
        }
      }
    }
  }
}

int resize_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst, uint32_t h_dst,
                       uint32_t c_cnt, uint32_t tensor_format, enum interpolation_mode interpolation) {
  switch (interpolation) {
    case BILINEAR:
      bilinear_interpolation_float16_rvv(src, dst, w_src, h_src, w_dst, h_dst, c_cnt, tensor_format);
      break;
    default:
      return -1;
  }

  return 0;
}

void bilinear_interpolation_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst,
                                        uint32_t h_dst, uint32_t c_cnt, uint32_t format) {
  // Height and width scaling factor
  _Float16 x_scale_factor = (_Float16)w_src / (_Float16)w_dst;
  _Float16 y_scale_factor = (_Float16)h_src / (_Float16)h_dst;

  // Address calculation constants
  uint32_t src_base_addr_incr = format == TENSOR_FORMAT_NCHW ? h_src * w_src : 1;
  uint32_t dst_base_addr_incr = format == TENSOR_FORMAT_NCHW ? h_dst * w_dst : 1;
  uint32_t addr_multiplier    = format == TENSOR_FORMAT_NCHW ? 1 : c_cnt;
  uint32_t load_bstride       = addr_multiplier * sizeof(_Float16);

  for (uint32_t c = 0; c < c_cnt; c++) {
    // Current vector length
    uint64_t vl;

    for (uint32_t x = 0; x < w_dst; x += vl) {
      vl               = __riscv_vsetvl_e16m2(w_dst - x);
      // Calculate points to interpolate on x-axis of input image
      vuint16m2_t id   = __riscv_vid_v_u16m2(vl);
      id               = __riscv_vadd_vx_u16m2(id, x, vl);
      vfloat16m2_t vx  = __riscv_vfcvt_f_xu_v_f16m2(id, vl);
      vfloat16m2_t vxp = __riscv_vfmax_vf_f16m2(
          __riscv_vfsub_vf_f16m2(__riscv_vfmul_vf_f16m2(__riscv_vfadd_vf_f16m2(vx, 0.5, vl), x_scale_factor, vl), 0.5,
                                 vl),
          0.0, vl);
      // // X-grid surrounding interpolation point
      vuint16m2_t  vx1    = __riscv_vfcvt_xu_f_v_u16m2(vxp, vl);
      vuint16m2_t  vx2    = __riscv_vminu_vx_u16m2(__riscv_vadd_vx_u16m2(vx1, 1, vl), w_src - 1, vl);
      // // Distance of xp to x-grid
      vfloat16m2_t x1_div = __riscv_vfsub_vv_f16m2(vxp, __riscv_vfcvt_f_xu_v_f16m2(vx1, vl), vl);
      vfloat16m2_t x2_div = __riscv_vfrsub_vf_f16m2(x1_div, 1.0, vl);

      // Output base addr
      _Float16 *dst_ptr = dst + x * addr_multiplier;

      // Previous y-row addr
      uint32_t y2_old = (uint32_t)-1;

      // Row linear interpolation results
      vfloat16m2_t r1, r2;

      for (uint32_t y = 0; y < h_dst; y++) {
        // Calculate point to interpolate on y-axis of input image
        _Float16 yp     = MAX((y + 0.5f) * (float)y_scale_factor - 0.5f, 0.0f);
        // Y-grid surrounding interpolation point
        uint32_t y1     = (uint32_t)yp;
        uint32_t y2     = MIN(y1 + 1, h_src - 1);
        // Distances of yp to y-grid
        _Float16 y1_div = yp - (_Float16)y1;
        _Float16 y2_div = (_Float16)1.0f - y1_div;

        // Y-row base addr
        _Float16 *row1_src = src + y1 * w_src * addr_multiplier;
        _Float16 *row2_src = src + y2 * w_src * addr_multiplier;

        if (y2_old == y1) {
          // Reuse one row
          r1 = __riscv_vmv_v_v_f16m2(r2, vl);

          // Get pixel values surrounding xp and yp
          vfloat16m2_t q12 = __riscv_vluxei16_v_f16m2(row2_src, __riscv_vmul_vx_u16m2(vx1, load_bstride, vl), vl);
          vfloat16m2_t q22 = __riscv_vluxei16_v_f16m2(row2_src, __riscv_vmul_vx_u16m2(vx2, load_bstride, vl), vl);

          // Calculate linear interpolation of second row
          r2 = __riscv_vfmacc_vv_f16m2(__riscv_vfmul_vv_f16m2(q22, x1_div, vl), q12, x2_div, vl);
        } else {
          // Reload both rows

          // Get pixel values surrounding xp and yp
          vfloat16m2_t q11 = __riscv_vluxei16_v_f16m2(row1_src, __riscv_vmul_vx_u16m2(vx1, load_bstride, vl), vl);
          vfloat16m2_t q21 = __riscv_vluxei16_v_f16m2(row1_src, __riscv_vmul_vx_u16m2(vx2, load_bstride, vl), vl);
          vfloat16m2_t q12 = __riscv_vluxei16_v_f16m2(row2_src, __riscv_vmul_vx_u16m2(vx1, load_bstride, vl), vl);
          vfloat16m2_t q22 = __riscv_vluxei16_v_f16m2(row2_src, __riscv_vmul_vx_u16m2(vx2, load_bstride, vl), vl);

          // Calculate linear interpolation of rows
          r1 = __riscv_vfmacc_vv_f16m2(__riscv_vfmul_vv_f16m2(q21, x1_div, vl), q11, x2_div, vl);
          r2 = __riscv_vfmacc_vv_f16m2(__riscv_vfmul_vv_f16m2(q22, x1_div, vl), q12, x2_div, vl);
        }

        // Calculate bilinear interpolation between rows
        vfloat16m2_t p = __riscv_vfmacc_vf_f16m2(__riscv_vfmul_vf_f16m2(r2, y1_div, vl), y2_div, r1, vl);

        // Store result
        if (format == TENSOR_FORMAT_NCHW) {
          __riscv_vse16_v_f16m2(dst_ptr, p, vl);
        } else {
          __riscv_vsse16_v_f16m2(dst_ptr, c_cnt * sizeof(_Float16), p, vl);
        }

        // Increment store base addr
        dst_ptr += addr_multiplier * w_dst;

        // Set old row addr
        y2_old = y2;
      }
    }
    // Increment pointer to base addresses
    src += src_base_addr_incr;
    dst += dst_base_addr_incr;
  }
}
