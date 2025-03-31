// Description: Color space conversion kernels
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#include <color_space.h>
#include <riscv_vector.h>
#include <string.h>

#define MIN(x, y) (x < y ? x : y)
#define MAX(x, y) (x > y ? x : y)

////////////
// Scalar //
////////////

void cspace_conversion(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, enum cspace_conversion conversion) {
  switch (conversion) {
    case YUV2RGB:
      yuv_to_rgb(src, dst, w, h, yuv2rgb_constants);
      break;
    case YCC2RGB:
      yuv_to_rgb(src, dst, w, h, ycc2rgb_constants);
      break;
    case YUV2GRAY:
      channel_extraction(src, dst, w, h, 3, 0);
      break;
    case RGB2YUV:
      common_cspace_conversion(src, dst, w, h, rgb2yuv_constants);
      break;
    case RGB2YCC:
      common_cspace_conversion(src, dst, w, h, rgb2ycc_constants);
      break;
    case RGB2GRAY:
      rgb_to_gray(src, dst, w, h);
    default:;
  }
}

void common_cspace_conversion(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants) {
  for (uint32_t hi = 0; hi < h; hi++) {
    for (uint32_t wi = 0; wi < w; wi++) {
      float a_ = (float)*src++ - constants[3][0];
      float b_ = (float)*src++ - constants[3][1];
      float c_ = (float)*src++ - constants[3][2];

      *dst++ = (uint8_t)MIN(
          MAX((constants[0][0] * a_ + constants[0][1] * b_ + constants[0][2] * c_ + constants[4][0] + 0.5f), 0), 255);
      *dst++ = (uint8_t)MIN(
          MAX((constants[1][0] * a_ + constants[1][1] * b_ + constants[1][2] * c_ + constants[4][1] + 0.5f), 0), 255);
      *dst++ = (uint8_t)MIN(
          MAX((constants[2][0] * a_ + constants[2][1] * b_ + constants[2][2] * c_ + constants[4][2] + 0.5f), 0), 255);
    }
  }
}

void yuv_to_rgb(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants) {
  for (uint32_t hi = 0; hi < h; hi++) {
    for (uint32_t wi = 0; wi < w; wi++) {
      float y_  = (float)*src++ - constants[3][0];
      float cb_ = (float)*src++ - constants[3][1];
      float cr_ = (float)*src++ - constants[3][2];

      // Calculate channels and saturate cast to uint8
      // +0.5 to round to nearest
      *dst++ = (uint8_t)MIN(MAX((y_ + constants[0][2] * cr_ + 0.5f), 0), 255);
      *dst++ = (uint8_t)MIN(MAX((y_ + constants[1][1] * cb_ + constants[1][2] * cr_ + 0.5f), 0), 255);
      *dst++ = (uint8_t)MIN(MAX((y_ + constants[2][1] * cb_ + 0.5f), 0), 255);
    }
  }
}

void rgb_to_gray(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h) {
  for (uint32_t hi = 0; hi < h; hi++) {
    for (uint32_t wi = 0; wi < w; wi++) {
      _Float16 r = (_Float16)*src++;
      _Float16 g = (_Float16)*src++;
      _Float16 b = (_Float16)*src++;

      // Calculate gray channel and cast to uint8
      *dst++ = (uint8_t)(0.299f * (float)r + 0.587f * (float)g + 0.114f * (float)b);
    }
  }
}

void channel_extraction(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, uint32_t c, uint32_t channel) {
  // Go to desired channel
  src += channel;

  for (uint32_t hi = 0; hi < h; hi++) {
    for (uint32_t wi = 0; wi < w; wi++) {
      // Extract channel
      *dst++ = *src;

      // Go to next value of channel
      src += c;
    }
  }
}

/////////
// RVV //
/////////

void cspace_conversion_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, enum cspace_conversion conversion) {
  switch (conversion) {
    case YUV2RGB:
      yuv_to_rgb_rvv(src, dst, w, h, yuv2rgb_constants);
      break;
    case YCC2RGB:
      yuv_to_rgb_rvv(src, dst, w, h, ycc2rgb_constants);
      break;
    case YUV2GRAY:
      channel_extraction_rvv(src, dst, w, h, 3, 0);
      break;
    case RGB2YUV:
      common_cspace_conversion_rvv(src, dst, w, h, rgb2yuv_constants);
      break;
    case RGB2YCC:
      common_cspace_conversion_rvv(src, dst, w, h, rgb2ycc_constants);
      break;
    case RGB2GRAY:
      rgb_to_gray_rvv(src, dst, w, h);
    default:;
  }
}

void common_cspace_conversion_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants) {
  int avl = h * w;
  while (avl > 0) {
    uint32_t vl = __riscv_vsetvl_e8m1(avl);

    // Load Y, Cb, Cr channels
    vuint8m1x3_t vsrc = __riscv_vlseg3e8_v_u8m1x3(src, vl);
    vuint8m1_t   a = __riscv_vget_v_u8m1x3_u8m1(vsrc, 0), b = __riscv_vget_v_u8m1x3_u8m1(vsrc, 1),
               c = __riscv_vget_v_u8m1x3_u8m1(vsrc, 2);

    // Convert to floats
    vfloat32m4_t a_ = __riscv_vfwsub_vf_f32m4(__riscv_vfwcvt_f_xu_v_f16m2(a, vl), constants[3][0], vl);
    vfloat32m4_t b_ = __riscv_vfwsub_vf_f32m4(__riscv_vfwcvt_f_xu_v_f16m2(b, vl), constants[3][1], vl);
    vfloat32m4_t c_ = __riscv_vfwsub_vf_f32m4(__riscv_vfwcvt_f_xu_v_f16m2(c, vl), constants[3][2], vl);

    // Calculate outputs
    vfloat32m4_t a__ = __riscv_vfadd_vf_f32m4(
        __riscv_vfmacc_vf_f32m4(
            __riscv_vfmacc_vf_f32m4(__riscv_vfmul_vf_f32m4(a_, constants[0][0], vl), constants[0][1], b_, vl),
            constants[0][2], c_, vl),
        constants[4][0], vl);
    vfloat32m4_t b__ = __riscv_vfadd_vf_f32m4(
        __riscv_vfmacc_vf_f32m4(
            __riscv_vfmacc_vf_f32m4(__riscv_vfmul_vf_f32m4(a_, constants[1][0], vl), constants[1][1], b_, vl),
            constants[1][2], c_, vl),
        constants[4][1], vl);
    vfloat32m4_t c__ = __riscv_vfadd_vf_f32m4(
        __riscv_vfmacc_vf_f32m4(
            __riscv_vfmacc_vf_f32m4(__riscv_vfmul_vf_f32m4(a_, constants[2][0], vl), constants[2][1], b_, vl),
            constants[2][2], c_, vl),
        constants[4][2], vl);

    // Saturate to uint8 range
    vfloat32m4_t a_sat = __riscv_vfmin_vf_f32m4(__riscv_vfmax_vf_f32m4(a__, 0.0, vl), 255.0, vl);
    vfloat32m4_t b_sat = __riscv_vfmin_vf_f32m4(__riscv_vfmax_vf_f32m4(b__, 0.0, vl), 255.0, vl);
    vfloat32m4_t c_sat = __riscv_vfmin_vf_f32m4(__riscv_vfmax_vf_f32m4(c__, 0.0, vl), 255.0, vl);

    // Convert float32 to uint8
    vuint8m1_t a_uint = __riscv_vncvt_x_x_w_u8m1(__riscv_vfncvt_xu_f_w_u16m2(a_sat, vl), vl);
    vuint8m1_t b_uint = __riscv_vncvt_x_x_w_u8m1(__riscv_vfncvt_xu_f_w_u16m2(b_sat, vl), vl);
    vuint8m1_t c_uint = __riscv_vncvt_x_x_w_u8m1(__riscv_vfncvt_xu_f_w_u16m2(c_sat, vl), vl);

    // Store R, G, B channels back
    // TODO replace with __riscv_vcreate_v_f16m1x4() when it becomes available
    vuint8m1x3_t vdst = __riscv_vundefined_u8m1x3();
    vdst = __riscv_vset_v_u8m1_u8m1x3(vdst, 0, a_uint);
    vdst = __riscv_vset_v_u8m1_u8m1x3(vdst, 1, b_uint);
    vdst = __riscv_vset_v_u8m1_u8m1x3(vdst, 2, c_uint);
    __riscv_vsseg3e8_v_u8m1x3(dst, vdst, vl);

    // Calculate next pointers and calculate remaining vl
    src += vl * 3;
    dst += vl * 3;
    avl -= vl;
  }
}

void yuv_to_rgb_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants) {
  int avl = h * w;
  while (avl > 0) {
    uint32_t vl = __riscv_vsetvl_e8m1(avl);

    // Load Y, Cb, Cr channels
    vuint8m1x3_t vsrc = __riscv_vlseg3e8_v_u8m1x3(src, vl);
    vuint8m1_t   y = __riscv_vget_v_u8m1x3_u8m1(vsrc, 0), cb = __riscv_vget_v_u8m1x3_u8m1(vsrc, 1),
               cr = __riscv_vget_v_u8m1x3_u8m1(vsrc, 2);

    // Convert to floats
    vfloat32m4_t y_  = __riscv_vfwsub_vf_f32m4(__riscv_vfwcvt_f_xu_v_f16m2(y, vl), constants[3][0], vl);
    vfloat32m4_t cb_ = __riscv_vfwsub_vf_f32m4(__riscv_vfwcvt_f_xu_v_f16m2(cb, vl), constants[3][1], vl);
    vfloat32m4_t cr_ = __riscv_vfwsub_vf_f32m4(__riscv_vfwcvt_f_xu_v_f16m2(cr, vl), constants[3][2], vl);

    // Calculate outputs
    vfloat32m4_t r = __riscv_vfmacc_vf_f32m4(y_, constants[0][2], cr_, vl);
    vfloat32m4_t g =
        __riscv_vfmacc_vf_f32m4(__riscv_vfmacc_vf_f32m4(y_, constants[1][1], cb_, vl), constants[1][2], cr_, vl);
    vfloat32m4_t b = __riscv_vfmacc_vf_f32m4(y_, constants[2][1], cb_, vl);

    // Saturate to uint8 range
    vfloat32m4_t r_sat = __riscv_vfmin_vf_f32m4(__riscv_vfmax_vf_f32m4(r, 0.0, vl), 255.0, vl);
    vfloat32m4_t g_sat = __riscv_vfmin_vf_f32m4(__riscv_vfmax_vf_f32m4(g, 0.0, vl), 255.0, vl);
    vfloat32m4_t b_sat = __riscv_vfmin_vf_f32m4(__riscv_vfmax_vf_f32m4(b, 0.0, vl), 255.0, vl);

    // Convert float32 to uint8
    vuint8m1_t r_uint = __riscv_vfncvt_xu_f_w_u8m1(__riscv_vfncvt_rod_f_f_w_f16m2(r_sat, vl), vl);
    vuint8m1_t g_uint = __riscv_vfncvt_xu_f_w_u8m1(__riscv_vfncvt_rod_f_f_w_f16m2(g_sat, vl), vl);
    vuint8m1_t b_uint = __riscv_vfncvt_xu_f_w_u8m1(__riscv_vfncvt_rod_f_f_w_f16m2(b_sat, vl), vl);

    // Store R, G, B channels back
    // TODO replace with __riscv_vcreate_v_f16m1x4() when it becomes available
    vuint8m1x3_t vdst = __riscv_vundefined_u8m1x3();
    vdst = __riscv_vset_v_u8m1_u8m1x3(vdst, 0, r_uint);
    vdst = __riscv_vset_v_u8m1_u8m1x3(vdst, 1, g_uint);
    vdst = __riscv_vset_v_u8m1_u8m1x3(vdst, 2, b_uint);
    __riscv_vsseg3e8_v_u8m1x3(dst, vdst, vl);

    // Calculate next pointers and calculate remaining vl
    src += vl * 3;
    dst += vl * 3;
    avl -= vl;
  }
}

void rgb_to_gray_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h) {
  int avl = h * w;
  while (avl > 0) {
    uint32_t vl = __riscv_vsetvl_e8m2(avl);

    // Load Y, Cb, Cr channels
    vuint8m2x3_t vsrc = __riscv_vlseg3e8_v_u8m2x3(src, vl);
    vuint8m2_t   r = __riscv_vget_v_u8m2x3_u8m2(vsrc, 0), g = __riscv_vget_v_u8m2x3_u8m2(vsrc, 1),
               b = __riscv_vget_v_u8m2x3_u8m2(vsrc, 2);

    // Convert operands to fp16
    vfloat16m4_t r_ = __riscv_vfwcvt_f_xu_v_f16m4(r, vl);
    vfloat16m4_t g_ = __riscv_vfwcvt_f_xu_v_f16m4(g, vl);
    vfloat16m4_t b_ = __riscv_vfwcvt_f_xu_v_f16m4(b, vl);

    // Calculate the gray channel
    vfloat16m4_t gray = __riscv_vfmacc_vf_f16m4(
        __riscv_vfmacc_vf_f16m4(__riscv_vfmul_vf_f16m4(r_, 0.299f, vl), 0.587f, g_, vl), 0.114, b_, vl);

    // Cast to uint8 and store back
    vuint8m2_t gray_uint = __riscv_vfncvt_xu_f_w_u8m2(gray, vl);
    __riscv_vse8_v_u8m2(dst, gray_uint, vl);

    src += vl * 3;
    dst += vl;
    avl -= vl;
  }
}

void channel_extraction_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, uint32_t c, uint32_t channel) {
  // Go to desired channel
  src += channel;

  int avl = h * w;
  while (avl > 0) {
    uint32_t vl = __riscv_vsetvl_e8m4(avl);

    // Extract channel
    __riscv_vse8_v_u8m4(dst, __riscv_vlse8_v_u8m4(src, 3, vl), vl);

    // Go to next value of channel
    src += vl * c;
    dst += vl;
    avl -= vl;
  }
}
