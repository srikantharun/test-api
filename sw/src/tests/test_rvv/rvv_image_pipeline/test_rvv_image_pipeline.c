// Description: Test application for a pipeline of image processing kernels
// This test program verifies the functionality and performance of individual and merged image processing kernels.
// The test includes resizing, cropping, tensor format transformation, scaling, and normalization.
// Both scalar and RVV (RISC-V Vector) implementations are evaluated, and their execution times are compared.
// The results are validated against golden reference data with an allowable error margin due to differences in processing methods.

#include <stdint.h>
#include <color_space.h>
#include <conversion.h>
#include <crop.h>
#include <pre_proc_pipe_merged.h>
#include <printf.h>
#include <resize.h>
#include <statistics.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

// Constants
extern uint32_t image_h;
extern uint32_t image_w;
extern uint32_t image_c;
extern uint32_t resize_dim;
extern uint32_t crop_dim;

// Input data
extern _Float16 img_mean[];
extern _Float16 img_std[];
extern _Float16 image[];

// Golden reference
extern _Float16 golden[];

// Output
extern _Float16 output_resize[];
extern _Float16 output_crop[];
extern _Float16 output[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // We take a 512x512 pixel RGB input image. The values are arrange in the HWC format.
  // The input is resized to an 256x256 pixel image using a bilinear interpolation. A center
  // crop then cuts off the sides and we end up with a 224x224 pixel image. We then do a tensor
  // transformation from HWC to CHW format and scale the values from the initial [0,255] to the
  // [0,1] range. Finally we normalize all values using the values using predefined mean and
  // standard deviation values.

  // Our resize implementation does not support antialiasing. The pytorch resize method uses
  // the Pillow resize method underneath which always uses antialiasing (for pillow input images).
  // Therefore we get mismatches in the resize output (which for our input image is up to 22). This
  // will propagate further through the next stages and the result will deviate up to ~10% (or ~0.4)
  // from the golden reference.

  // Image pre-processing pipeline using individual kernels
  scalar_time = MEASURE(({
    resize_float16(image, output_resize, image_w, image_h, resize_dim, resize_dim, image_c, TENSOR_FORMAT_NHWC,BILINEAR);
    center_crop(output_resize, output_crop, resize_dim, resize_dim, image_c, crop_dim, crop_dim, TENSOR_FORMAT_NHWC);
    tensor_format_nhwc_to_nchw_float16(output_crop, output, 1, crop_dim, crop_dim, image_c);
    tensor_float16_scaled(output, output, 1, crop_dim, crop_dim, image_c, 255.0);
    instance_norm(output, 1, crop_dim, crop_dim, image_c, img_mean, img_std);
  }));
  CHECK_TRUE(compare_tensors_float16_with_error(golden, output, 1, crop_dim, crop_dim, image_c, 0.4f) == TEST_SUCCESS, "Scalar pipeline output does not match the golden reference");

  rvv_time = MEASURE(({
      resize_float16_rvv(image, output_resize, image_w, image_h, resize_dim, resize_dim, image_c, TENSOR_FORMAT_NHWC, BILINEAR);
      center_crop_rvv(output_resize, output_crop, resize_dim, resize_dim, image_c, crop_dim, crop_dim, TENSOR_FORMAT_NHWC);
      tensor_format_nhwc_to_nchw_float16_rvv(output_crop, output, 1, crop_dim, crop_dim, image_c);
      tensor_float16_scaled_rvv(output, output, 1, crop_dim, crop_dim, image_c, 255.0);
      instance_norm_rvv(output, 1, crop_dim, crop_dim, image_c, img_mean, img_std);
  }));
  CHECK_TRUE(compare_tensors_float16_with_error(golden, output, 1, crop_dim, crop_dim, image_c, 0.4f) == TEST_SUCCESS, "RVV pipeline output does not match the golden reference");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Merged image pre-processing pipeline
  scalar_time = MEASURE(({
      pre_proc_pipe_merged(image, output, image_w, image_h, resize_dim, resize_dim, crop_dim, crop_dim, img_mean, img_std);
  }));
  CHECK_TRUE(compare_tensors_float16_with_error(golden, output, 1, crop_dim, crop_dim, image_c, 0.4f) == TEST_SUCCESS, "Merged scalar pipeline output does not match the golden reference");

  rvv_time = MEASURE(({
      pre_proc_pipe_merged_rvv(image, output, image_w, image_h, resize_dim, resize_dim, crop_dim, crop_dim, img_mean, img_std);
  }));
  CHECK_TRUE(compare_tensors_float16_with_error(golden, output, 1, crop_dim, crop_dim, image_c, 0.4f) == TEST_SUCCESS, "Merged RVV pipeline output does not match the golden reference");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
