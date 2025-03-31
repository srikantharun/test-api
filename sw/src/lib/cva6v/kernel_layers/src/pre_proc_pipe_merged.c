// Description: Merged pre-processing pipeline kernel
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#include <riscv_vector.h>
#include <stdint.h>

#define MAX(x, y) (x < y ? y : x)
#define MIN(x, y) (x < y ? x : y)

int pre_proc_pipe_merged(_Float16 *image, _Float16 *output, uint32_t image_w, uint32_t image_h, uint32_t resize_w,
                         uint32_t resize_h, uint32_t crop_w, uint32_t crop_h, _Float16 *norm_mean, _Float16 *norm_std) {
  // This kernel only supports image downscaling
  if (image_w < resize_w || image_h < resize_h || image_w < crop_w || image_h < crop_h) return -1;

  // Height and width scaling factor
  _Float16 x_scale_factor = (_Float16)image_w / (_Float16)resize_w;
  _Float16 y_scale_factor = (_Float16)image_h / (_Float16)resize_h;

  // Center crop distances to top left corner
  uint32_t top_left_x = (uint32_t)((resize_w - crop_w) / 2.0f + 0.5f);
  uint32_t top_left_y = (uint32_t)((resize_h - crop_h) / 2.0f + 0.5f);

  // Value scale factor
  _Float16 scale_factor = 1.0 / 255.0;

  for (uint32_t c = 0; c < 3; c++) {
    for (uint32_t y = 0; y < crop_h; y++) {
      // Calculate point to interpolate on y-axis of input image
      _Float16 yp     = MAX((y + top_left_y + 0.5f) * (float)y_scale_factor - 0.5f, 0.0f);
      // Y-grid surrounding interpolation point
      uint32_t y1     = (uint32_t)yp;
      uint32_t y2     = MIN(y1 + 1, image_h - 1);
      // Distances of yp to y-grid
      _Float16 y1_div = yp - (_Float16)y1;

      for (uint32_t x = 0; x < crop_w; x++) {
        // Calculate point to interpolate on x-axis of input image
        _Float16 xp     = MAX((x + top_left_x + 0.5f) * (float)x_scale_factor - 0.5f, 0.0f);
        // X-grid surrounding interpolation point
        int32_t  x1     = (int32_t)xp;
        int32_t  x2     = MIN((uint32_t)x1 + 1, image_w - 1);
        // Distance of xp to x-grid
        _Float16 x1_div = xp - (_Float16)x1;

        // Calculate load addrs
        uint32_t q11_addr, q21_addr, q12_addr, q22_addr;
        q11_addr = y1 * image_w * 3 + x1 * 3 + c;
        q21_addr = y1 * image_w * 3 + x2 * 3 + c;
        q12_addr = y2 * image_w * 3 + x1 * 3 + c;
        q22_addr = y2 * image_w * 3 + x2 * 3 + c;

        // Get pixel values surrounding xp and yp
        _Float16 q11 = image[q11_addr];
        _Float16 q21 = image[q21_addr];
        _Float16 q12 = image[q12_addr];
        _Float16 q22 = image[q22_addr];

        // Calculate bilinear interpolation
        _Float16 r1 = q11 + (q21 - q11) * x1_div;
        _Float16 r2 = q12 + (q22 - q12) * x1_div;
        _Float16 p  = r1 + (r2 - r1) * y1_div;

        // Scale to [0, 1] range
        _Float16 scale = p * scale_factor;

        // Instance norm
        _Float16 norm = (scale - norm_mean[c]) / norm_std[c];

        // Store result
        output[c * crop_h * crop_w + y * crop_w + x] = norm;
      }
    }
  }

  return 0;
}

int pre_proc_pipe_merged_rvv(_Float16 *image, _Float16 *output, uint32_t image_w, uint32_t image_h, uint32_t resize_w,
                             uint32_t resize_h, uint32_t crop_w, uint32_t crop_h, _Float16 *norm_mean,
                             _Float16 *norm_std) {
  // This kernel only supports image downscaling
  if (image_w < resize_w || image_h < resize_h || image_w < crop_w || image_h < crop_h) return -1;

  // Height and width scaling factor
  _Float16 x_scale_factor = (_Float16)image_w / (_Float16)resize_w;
  _Float16 y_scale_factor = (_Float16)image_h / (_Float16)resize_h;

  // Center crop distances to top left corner
  uint32_t top_left_x = (uint32_t)((resize_w - crop_w) / 2.0f + 0.5f);
  uint32_t top_left_y = (uint32_t)((resize_h - crop_h) / 2.0f + 0.5f);

  // Value scale factor
  _Float16 scale_factor = 1.0 / 255.0;

  // Address calculation constants
  uint32_t load_bstride = 3 * sizeof(_Float16);
  uint32_t store_c_diff = crop_h * crop_w;

  // Current vector length
  uint64_t vl;

  // Reciprocal normalized standard deviation
  _Float16 std_div0 = 1.0f / (float)norm_std[0];
  _Float16 std_div1 = 1.0f / (float)norm_std[1];
  _Float16 std_div2 = 1.0f / (float)norm_std[2];

  for (uint32_t x = 0; x < crop_w; x += vl) {
    vl               = __riscv_vsetvl_e16m2(crop_w - x);
    // Calculate points to interpolate on x-axis of input image
    vuint16m2_t id   = __riscv_vid_v_u16m2(vl);
    id               = __riscv_vadd_vx_u16m2(id, x, vl);
    vfloat16m2_t vx  = __riscv_vfcvt_f_xu_v_f16m2(__riscv_vadd_vx_u16m2(id, top_left_x, vl), vl);
    vfloat16m2_t vxp = __riscv_vfmax_vf_f16m2(
        __riscv_vfsub_vf_f16m2(__riscv_vfmul_vf_f16m2(__riscv_vfadd_vf_f16m2(vx, 0.5, vl), x_scale_factor, vl), 0.5,
                               vl),
        0.0, vl);
    // // X-grid surrounding interpolation point
    vuint16m2_t  vx1    = __riscv_vfcvt_xu_f_v_u16m2(vxp, vl);
    vuint16m2_t  vx2    = __riscv_vminu_vx_u16m2(__riscv_vadd_vx_u16m2(vx1, 1, vl), image_w - 1, vl);
    // // Distance of xp to x-grid
    vfloat16m2_t x1_div = __riscv_vfsub_vv_f16m2(vxp, __riscv_vfcvt_f_xu_v_f16m2(vx1, vl), vl);

    // Output base addr
    _Float16 *output_ptr = output + x;

    // Previous y-row addr
    uint32_t y2_old = (uint32_t)-1;

    // Row linear interpolation results
    vfloat16m2_t r1_r, r1_g, r1_b, r2_r, r2_g, r2_b;

    for (uint32_t y = 0; y < crop_h; y++) {
      // Calculate point to interpolate on y-axis of input image
      _Float16 yp     = MAX((y + top_left_y + 0.5f) * (float)y_scale_factor - 0.5f, 0.0f);
      // Y-grid surrounding interpolation point
      uint32_t y1     = (uint32_t)yp;
      uint32_t y2     = MIN(y1 + 1, image_h - 1);
      // Distances of yp to y-grid
      _Float16 y1_div = yp - (_Float16)y1;

      // Y-row base addr
      _Float16 *row1_image = image + y1 * image_w * 3;
      _Float16 *row2_image = image + y2 * image_w * 3;

      if (y2_old == y1) {
        // Reuse one row
        r1_r = __riscv_vmv_v_v_f16m2(r2_r, vl);
        r1_g = __riscv_vmv_v_v_f16m2(r2_g, vl);
        r1_b = __riscv_vmv_v_v_f16m2(r2_b, vl);

        // Get pixel values surrounding xp and yp
        vfloat16m2x3_t q12 =
                           __riscv_vluxseg3ei16_v_f16m2x3(row2_image, __riscv_vmul_vx_u16m2(vx1, load_bstride, vl), vl),
                       q22 =
                           __riscv_vluxseg3ei16_v_f16m2x3(row2_image, __riscv_vmul_vx_u16m2(vx2, load_bstride, vl), vl);
        vfloat16m2_t q12_r = __riscv_vget_v_f16m2x3_f16m2(q12, 0), q12_g = __riscv_vget_v_f16m2x3_f16m2(q12, 1),
                     q12_b = __riscv_vget_v_f16m2x3_f16m2(q12, 2), q22_r = __riscv_vget_v_f16m2x3_f16m2(q22, 0),
                     q22_g = __riscv_vget_v_f16m2x3_f16m2(q22, 1), q22_b = __riscv_vget_v_f16m2x3_f16m2(q22, 2);

        // Calculate linear interpolation of second row
        r2_r = __riscv_vfmacc_vv_f16m2(q12_r, __riscv_vfsub_vv_f16m2(q22_r, q12_r, vl), x1_div, vl);
        r2_g = __riscv_vfmacc_vv_f16m2(q12_g, __riscv_vfsub_vv_f16m2(q22_g, q12_g, vl), x1_div, vl);
        r2_b = __riscv_vfmacc_vv_f16m2(q12_b, __riscv_vfsub_vv_f16m2(q22_b, q12_b, vl), x1_div, vl);
      } else {
        // Reload both rows

        // Get pixel values surrounding xp and yp of first row
        vfloat16m2x3_t q11 =
                           __riscv_vluxseg3ei16_v_f16m2x3(row1_image, __riscv_vmul_vx_u16m2(vx1, load_bstride, vl), vl),
                       q21 =
                           __riscv_vluxseg3ei16_v_f16m2x3(row1_image, __riscv_vmul_vx_u16m2(vx2, load_bstride, vl), vl);
        vfloat16m2_t q11_r = __riscv_vget_v_f16m2x3_f16m2(q11, 0), q11_g = __riscv_vget_v_f16m2x3_f16m2(q11, 1),
                     q11_b = __riscv_vget_v_f16m2x3_f16m2(q11, 2), q21_r = __riscv_vget_v_f16m2x3_f16m2(q21, 0),
                     q21_g = __riscv_vget_v_f16m2x3_f16m2(q21, 1), q21_b = __riscv_vget_v_f16m2x3_f16m2(q21, 2);

        // Calculate linear interpolation of first row
        r1_r = __riscv_vfmacc_vv_f16m2(q11_r, __riscv_vfsub_vv_f16m2(q21_r, q11_r, vl), x1_div, vl);
        r1_g = __riscv_vfmacc_vv_f16m2(q11_g, __riscv_vfsub_vv_f16m2(q21_g, q11_g, vl), x1_div, vl);
        r1_b = __riscv_vfmacc_vv_f16m2(q11_b, __riscv_vfsub_vv_f16m2(q21_b, q11_b, vl), x1_div, vl);

        // Get pixel values surrounding xp and yp of second row
        vfloat16m2x3_t q12 =
                           __riscv_vluxseg3ei16_v_f16m2x3(row2_image, __riscv_vmul_vx_u16m2(vx1, load_bstride, vl), vl),
                       q22 =
                           __riscv_vluxseg3ei16_v_f16m2x3(row2_image, __riscv_vmul_vx_u16m2(vx2, load_bstride, vl), vl);
        vfloat16m2_t q12_r = __riscv_vget_v_f16m2x3_f16m2(q12, 0), q12_g = __riscv_vget_v_f16m2x3_f16m2(q12, 1),
                     q12_b = __riscv_vget_v_f16m2x3_f16m2(q12, 2), q22_r = __riscv_vget_v_f16m2x3_f16m2(q22, 0),
                     q22_g = __riscv_vget_v_f16m2x3_f16m2(q22, 1), q22_b = __riscv_vget_v_f16m2x3_f16m2(q22, 2);

        // Calculate linear interpolation of second row
        r2_r = __riscv_vfmacc_vv_f16m2(q12_r, __riscv_vfsub_vv_f16m2(q22_r, q12_r, vl), x1_div, vl);
        r2_g = __riscv_vfmacc_vv_f16m2(q12_g, __riscv_vfsub_vv_f16m2(q22_g, q12_g, vl), x1_div, vl);
        r2_b = __riscv_vfmacc_vv_f16m2(q12_b, __riscv_vfsub_vv_f16m2(q22_b, q12_b, vl), x1_div, vl);
      }

      // Calculate bilinear interpolation between rows
      vfloat16m2_t p_r = __riscv_vfmacc_vf_f16m2(r1_r, y1_div, __riscv_vfsub_vv_f16m2(r2_r, r1_r, vl), vl);
      vfloat16m2_t p_g = __riscv_vfmacc_vf_f16m2(r1_g, y1_div, __riscv_vfsub_vv_f16m2(r2_g, r1_g, vl), vl);
      vfloat16m2_t p_b = __riscv_vfmacc_vf_f16m2(r1_b, y1_div, __riscv_vfsub_vv_f16m2(r2_b, r1_b, vl), vl);

      // Scale to [0, 1] range
      vfloat16m2_t scale_r = __riscv_vfmul_vf_f16m2(p_r, scale_factor, vl);
      vfloat16m2_t scale_g = __riscv_vfmul_vf_f16m2(p_g, scale_factor, vl);
      vfloat16m2_t scale_b = __riscv_vfmul_vf_f16m2(p_b, scale_factor, vl);

      // Instance norm
      vfloat16m2_t norm_r = __riscv_vfmul_vf_f16m2(__riscv_vfsub_vf_f16m2(scale_r, norm_mean[0], vl), std_div0, vl);
      vfloat16m2_t norm_g = __riscv_vfmul_vf_f16m2(__riscv_vfsub_vf_f16m2(scale_g, norm_mean[1], vl), std_div1, vl);
      vfloat16m2_t norm_b = __riscv_vfmul_vf_f16m2(__riscv_vfsub_vf_f16m2(scale_b, norm_mean[2], vl), std_div2, vl);

      // Store result
      __riscv_vse16_v_f16m2(output_ptr, norm_r, vl);
      __riscv_vse16_v_f16m2(output_ptr + store_c_diff, norm_g, vl);
      __riscv_vse16_v_f16m2(output_ptr + 2 * store_c_diff, norm_b, vl);

      // Increment store base addr
      output_ptr += crop_w;

      // Set old row addr
      y2_old = y2;
    }
  }

  return 0;
}
