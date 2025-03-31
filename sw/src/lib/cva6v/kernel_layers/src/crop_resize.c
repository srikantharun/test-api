// Description: Crop and resize kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <crop_resize.h>
#include <riscv_vector.h>


static void crop_resize_rvv_init(long w, long c, long rsz_w, uint16_t *x_offset, uint16_t *x_diff) {
  // for each column of the resized image, calculate the byte offset of the
  // corresponding source image column (i.e., the source image column that
  // immediatly preceeds the exact location of the resized image column) and the
  // difference between the x coordinate of the resized image column and source
  // image column (that difference is in the range 0 to 1, and scaled by 256)
  for (long rsz_x = 0; rsz_x < rsz_w; rsz_x++) {
    // 2 rsz_w times the x coordinate of the current column of the resized image
    // in source image coordinates
    long _2rszw_colx = 2 * w * rsz_x + w - rsz_w;

    // index of the source image column immediately preceeding that x coordinate
    long col_idx    = _2rszw_colx / (2 * rsz_w);
    x_offset[rsz_x] = col_idx * c;  // byte offset of that column

    // difference between the x coordinate of the source image column and the x
    // coordinate of the corresponding column in the resized image (scaled by
    // 2*rsz_w)
    long _2rszw_diff = _2rszw_colx % (2 * rsz_w);
    x_diff[rsz_x]    = (_2rszw_diff * 4096) / (2 * rsz_w);  // difference scaled by 4096
  }
}

void crop_resize_rvv(const uint8_t *src, uint8_t *dst, long h, long w, long c, long rsz_h, long rsz_w,
                     long crp_h, long crp_w) {
  uint16_t x_offset[rsz_w];
  uint16_t x_diff[rsz_w];
  crop_resize_rvv_init(w, c, rsz_w, x_offset, x_diff);

  size_t vl;
  for (long crp_x = 0; crp_x < crp_w; crp_x += vl) {
    vl = __riscv_vsetvl_e8m1(crp_w - crp_x);

    long rsz_x = crp_x + (rsz_w - crp_w) / 2;

    // fetch the byte offsets of the source image columns corresponding to each
    // column of the resized image
    vuint16m2_t rsz_off_v = __riscv_vle16_v_u16m2(&x_offset[rsz_x], vl);

    // fetch the difference between the x coordinates of the columns of the
    // resized image and the corresponding source image columns and calculate
    // the difference between the column of the resized image and the next
    // source image column (note: differences are scaled by 4096)
    vuint16m2_t x1_diff_v = __riscv_vle16_v_u16m2(&x_diff[rsz_x], vl),
                x2_diff_v = __riscv_vrsub_vx_u16m2(x1_diff_v, 4096, vl);

    for (long crp_y = 0; crp_y < crp_h; crp_y++) {
      long rsz_y = crp_y + (rsz_h - crp_h) / 2;

      // 2 rsz_h times the y coordinate of the current row of the resized image
      // in source image coordinates (calculation analoguous to the x
      // coordinates in crop_resize_rvv_init())
      long _2rszh_rowy = 2 * h * rsz_y + h - rsz_h;

      // source image rows surrounding the current destination image row
      long y1 = _2rszh_rowy / (2 * rsz_h), y2 = y1 + 1;

      // y2 is invalid for the last row, but pixels from this row will be
      // multiplied by 0 anyways
      if (y2 == h) {
        y2--;
      }

      // difference between the actual y coordinate and pixels y1 and y2, scaled
      // by 4096
      long y1_diff = ((_2rszh_rowy % (2 * rsz_h)) * 4096) / (2 * rsz_h), y2_diff = 4096 - y1_diff;

      for (long z = 0; z < c; z++) {
        // load the surrounding source image pixels
        vuint8m1_t q11_v8, q12_v8, q21_v8, q22_v8;
        q11_v8 = __riscv_vluxei16_v_u8m1(src + z + c * (w * y1), rsz_off_v, vl);
        q12_v8 = __riscv_vluxei16_v_u8m1(src + z + c * (1 + w * y1), rsz_off_v, vl);
        q21_v8 = __riscv_vluxei16_v_u8m1(src + z + c * (w * y2), rsz_off_v, vl);
        q22_v8 = __riscv_vluxei16_v_u8m1(src + z + c * (1 + w * y2), rsz_off_v, vl);

        // extend the 8-bit source data to 16-bit
        vuint16m2_t q11_v16, q12_v16, q21_v16, q22_v16;
        q11_v16 = __riscv_vzext_vf2_u16m2(q11_v8, vl);
        q12_v16 = __riscv_vzext_vf2_u16m2(q12_v8, vl);
        q21_v16 = __riscv_vzext_vf2_u16m2(q21_v8, vl);
        q22_v16 = __riscv_vzext_vf2_u16m2(q22_v8, vl);

        // linear interpolation in the x direction
        vuint32m4_t r1_v, r2_v;
        r1_v = __riscv_vwmulu_vv_u32m4(q11_v16, x2_diff_v, vl);
        r2_v = __riscv_vwmulu_vv_u32m4(q21_v16, x2_diff_v, vl);
        r1_v = __riscv_vwmaccu_vv_u32m4(r1_v, q12_v16, x1_diff_v, vl);
        r2_v = __riscv_vwmaccu_vv_u32m4(r2_v, q22_v16, x1_diff_v, vl);

        // linear interpolation in the y direction
        vuint32m4_t p_v;
        p_v = __riscv_vmul_vx_u32m4(r1_v, y2_diff, vl);
        p_v = __riscv_vmacc_vx_u32m4(p_v, y1_diff, r2_v, vl);

        // quantization: divide by the scaling of the differences between
        // coordinates (i.e., two times 4096), implemented by two narrowing
        // right shifts
        vuint16m2_t p_v16;
        p_v16 = __riscv_vnsrl_wx_u16m2(p_v, 24, vl);
        vuint8m1_t p_v8;
        p_v8 = __riscv_vnsrl_wx_u8m1(p_v16, 0, vl);

        // store result
        __riscv_vsse8_v_u8m1(dst + z + c * (crp_x + crp_w * crp_y), c, p_v8, vl);
      }
    }
  }
}
