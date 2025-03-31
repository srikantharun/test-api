// Description: Test application for crop and resize kernels.
// This application tests various kernels such as cropping, center cropping, and resizing on both
// NCHW (Channel First) and NHWC (Channel Last) tensor formats. It verifies the correctness of the
// implemented functions by comparing the output with golden reference data using test utility functions.

#include <stdint.h>
#include <crop.h>
#include <printf.h>
#include <resize.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

// Constants
extern const int32_t W_SRC;
extern const int32_t H_SRC;
extern const int32_t W_DST;
extern const int32_t H_DST;
extern const int32_t C;
extern const int32_t TOP_LEFT_X;
extern const int32_t TOP_LEFT_Y;


// Input / output data
extern _Float16 image_nchw[];
extern _Float16 image_nhwc[];
extern _Float16 output[];

// Golden references
extern _Float16 golden_crop_nhwc[];
extern _Float16 golden_crop_nchw[];
extern _Float16 golden_center_crop_nhwc[];
extern _Float16 golden_resize_hwc[];
extern _Float16 golden_resize_chw[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // Crop HWC image
  scalar_time = MEASURE(crop(image_nhwc, output, H_SRC, W_SRC, C, H_DST, W_DST, TOP_LEFT_X, TOP_LEFT_Y, TENSOR_FORMAT_NHWC));
  CHECK_TRUE(compare_tensors_float16(golden_crop_nhwc, output, 1, H_DST, W_DST, C) == TEST_SUCCESS, "HWC Crop failed");
  rvv_time = MEASURE(crop_rvv(image_nhwc, output, H_SRC, W_SRC, C, H_DST, W_DST, TOP_LEFT_X, TOP_LEFT_Y, TENSOR_FORMAT_NHWC));
  CHECK_TRUE(compare_tensors_float16(golden_crop_nhwc, output, 1, H_DST, W_DST, C) == TEST_SUCCESS, "HWC Crop RVV failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Crop CHW image
  scalar_time = MEASURE(crop(image_nchw, output, H_SRC, W_SRC, C, H_DST, W_DST, TOP_LEFT_X, TOP_LEFT_Y, TENSOR_FORMAT_NCHW));
  CHECK_TRUE(compare_tensors_float16(golden_crop_nchw, output, 1, H_DST, W_DST, C) == TEST_SUCCESS, "CHW Crop failed");
  rvv_time = MEASURE(crop_rvv(image_nchw, output, H_SRC, W_SRC, C, H_DST, W_DST, TOP_LEFT_X, TOP_LEFT_Y, TENSOR_FORMAT_NCHW));
  CHECK_TRUE(compare_tensors_float16(golden_crop_nchw, output, 1, H_DST, W_DST, C) == TEST_SUCCESS, "CHW Crop RVV failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Center crop HWC image
  scalar_time = MEASURE(center_crop(image_nhwc, output, H_SRC, W_SRC, C, H_DST, W_DST, TENSOR_FORMAT_NHWC));
  CHECK_TRUE(compare_tensors_float16(golden_center_crop_nhwc, output, 1, H_DST, W_DST, C) == TEST_SUCCESS, "HWC Center Crop failed");
  rvv_time = MEASURE(center_crop_rvv(image_nhwc, output, H_SRC, W_SRC, C, H_DST, W_DST, TENSOR_FORMAT_NHWC));
  CHECK_TRUE(compare_tensors_float16(golden_center_crop_nhwc, output, 1, H_DST, W_DST, C) == TEST_SUCCESS, "HWC Center Crop RVV failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Resize CHW image
  scalar_time = MEASURE(resize_float16(image_nchw, output, W_SRC, H_SRC, W_DST, H_DST, C, TENSOR_FORMAT_NCHW, BILINEAR));
  CHECK_TRUE(compare_tensors_float16_with_error(golden_resize_chw, output, 1, H_DST, W_DST, C, 0.0f) == TEST_SUCCESS, "CHW Resize failed");
  rvv_time = MEASURE(resize_float16_rvv(image_nchw, output, W_SRC, H_SRC, W_DST, H_DST, C, TENSOR_FORMAT_NCHW, BILINEAR));
  CHECK_TRUE(compare_tensors_float16_with_error(golden_resize_chw, output, 1, H_DST, W_DST, C, 0.0f) == TEST_SUCCESS, "CHW Resize RVV failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Resize HWC image
  scalar_time = MEASURE(resize_float16(image_nhwc, output, W_SRC, H_SRC, W_DST, H_DST, C, TENSOR_FORMAT_NHWC, BILINEAR));
  CHECK_TRUE(compare_tensors_float16_with_error(golden_resize_hwc, output, 1, H_DST, W_DST, C, 0.0f) == TEST_SUCCESS, "HWC Resize failed");
  rvv_time = MEASURE(resize_float16_rvv(image_nhwc, output, W_SRC, H_SRC, W_DST, H_DST, C, TENSOR_FORMAT_NHWC, BILINEAR));
  CHECK_TRUE(compare_tensors_float16_with_error(golden_resize_hwc, output, 1, H_DST, W_DST, C, 0.0f) == TEST_SUCCESS, "HWC Resize RVV failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
