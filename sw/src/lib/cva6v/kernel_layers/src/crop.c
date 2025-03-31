// Description: Crop kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <crop.h>

#include <riscv_vector.h>

////////////
// Scalar //
////////////

int crop(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c, uint32_t crop_h,
         uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y, uint32_t format) {
  if (image_w < crop_w || image_h < crop_h) return -1;

  switch (format) {
    case TENSOR_FORMAT_NCHW:
      image_crop_chw(image, output, image_h, image_w, image_c, crop_h, crop_w, top_left_x, top_left_y);
      break;
    case TENSOR_FORMAT_NHWC:
      image_crop_hwc(image, output, image_h, image_w, image_c, crop_h, crop_w, top_left_x, top_left_y);
      break;
  }

  return 0;
}

int center_crop(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                uint32_t crop_h, uint32_t crop_w, uint32_t format) {
  uint32_t top_left_x = (uint32_t)((image_w - crop_w) / 2.0f + 0.5f);
  uint32_t top_left_y = (uint32_t)((image_h - crop_h) / 2.0f + 0.5f);
  UNUSED(image_h);

  return crop(image, output, image_h, image_w, image_c, crop_h, crop_w, top_left_x, top_left_y, format);
}

void image_crop_hwc(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                    uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y) {
  UNUSED(image_h);
  image                += (image_w * top_left_y + top_left_x) * image_c;
  _Float16 *output_ptr = output;

  for (uint32_t y = 0; y < crop_h; y++) {
    _Float16 *image_ptr = image;
    for (uint32_t x = 0; x < crop_w * image_c; x++) {
      *output_ptr++ = *image_ptr++;
    }
    image += image_w * image_c;
  }
}

void image_crop_chw(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                    uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y) {
  uint32_t plane_offset = (image_w * top_left_y + top_left_x);
  uint32_t cplane       = image_h * image_w;

  _Float16 *output_ptr = output;
  image                += plane_offset;
  _Float16 *_image_ptr = image;
  for (uint32_t ci = 0; ci < image_c; ci++) {
    _Float16 *image_ptr = image;
    for (uint32_t y = 0; y < crop_h; y++) {
      for (uint32_t x = 0; x < crop_w; x++) {
        *output_ptr++ = *image_ptr++;
      }
      image     += image_w;
      image_ptr = image;
    }
    _image_ptr += cplane;
    image      = _image_ptr;
  }
}

/////////
// RVV //
/////////

int crop_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c, uint32_t crop_h,
             uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y, uint32_t format) {
  if (image_w < crop_w || image_h < crop_h) return -1;

  switch (format) {
    case TENSOR_FORMAT_NCHW:
      image_crop_chw_rvv(image, output, image_h, image_w, image_c, crop_h, crop_w, top_left_x, top_left_y);
      break;
    case TENSOR_FORMAT_NHWC:
      image_crop_hwc_rvv(image, output, image_h, image_w, image_c, crop_h, crop_w, top_left_x, top_left_y);
      break;
  }

  return 0;
}

int center_crop_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                    uint32_t crop_h, uint32_t crop_w, uint32_t format) {
  uint32_t top_left_x = (uint32_t)((image_w - crop_w) / 2.0f + 0.5f);
  uint32_t top_left_y = (uint32_t)((image_h - crop_h) / 2.0f + 0.5f);
  UNUSED(image_h);

  return crop_rvv(image, output, image_h, image_w, image_c, crop_h, crop_w, top_left_x, top_left_y, format);
}

void image_crop_hwc_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                        uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y) {
  UNUSED(image_h);
  image += (image_w * top_left_y + top_left_x) * image_c;

  _Float16 *output_ptr = output;

  uint32_t crop_w_actual  = image_c * crop_w;
  uint32_t image_w_actual = image_c * image_w;
  uint32_t vl             = __riscv_vsetvl_e16m8(crop_w_actual);

  for (uint32_t y = 0; y < crop_h; y++) {
    _Float16 *image_ptr = image;
    for (uint32_t x = crop_w_actual; x > 0; x -= vl) {
      vl             = __riscv_vsetvl_e16m8(x);
      vfloat16m8_t v = __riscv_vle16_v_f16m8(image_ptr, vl);
      __riscv_vse16_v_f16m8(output_ptr, v, vl);

      image_ptr  += vl;
      output_ptr += vl;
    }
    vl    = __riscv_vsetvl_e16m8(crop_w_actual);
    image += image_w_actual;
  }
}

void image_crop_chw_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                        uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y) {
  image           += (image_w * top_left_y + top_left_x);
  uint32_t cplane = image_h * image_w;

  _Float16 *output_ptr = output;
  _Float16 *_image_ptr = image;

  uint32_t vl = __riscv_vsetvl_e16m8(crop_w);
  for (uint32_t ci = 0; ci < image_c; ci++) {
    _Float16 *image_ptr = image;
    for (uint32_t y = 0; y < crop_h; y++) {
      for (uint32_t x = crop_w; x > 0; x -= vl) {
        vl             = __riscv_vsetvl_e16m8(x);
        vfloat16m8_t v = __riscv_vle16_v_f16m8(image_ptr, vl);
        __riscv_vse16_v_f16m8(output_ptr, v, vl);

        image_ptr  += vl;
        output_ptr += vl;
      }
      image     += image_w;
      image_ptr = image;
    }
    _image_ptr += cplane;
    image      = _image_ptr;
  }
}
