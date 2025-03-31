// Description: Test application for color_space kernel
// This test program verifies various color space conversions  (YCC to RGB, RGB to YCC, YUV to RGB,
// RGB to YUV, YUV to Gray, RGB to Gray). Performs both scalar and RVV implementations and
// compares the output against golden models to ensure correctness with a small allowable
// error margin due to rounding differences.

#include <stdint.h>
#include <color_space.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

#define N 1
extern int32_t H;
extern int32_t W;
#define C 3

extern uint8_t input_rgb[];
extern uint8_t input_ycc[];
extern uint8_t input_yuv[];
extern uint8_t output[];
extern uint8_t golden_ycc[];
extern uint8_t golden_yuv[];
extern uint8_t golden_gray[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // Set FRM to RNE
  asm volatile("csrrwi x0, frm, 0");

  // We compare with an error of 1 due to small deviations in the coefficients used between
  // OpenCV (golden model) and our kernel, which leads to rounding errors.

  // YCC to RGB
  scalar_time = MEASURE(cspace_conversion(input_ycc, output, W, H, YCC2RGB));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_ycc, output, N, H, W, C, 1) == TEST_SUCCESS, "YCC to RGB conversion failed in scalar implementation");
  rvv_time = MEASURE(cspace_conversion_rvv(input_ycc, output, W, H, YCC2RGB));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_ycc, output, N, H, W, C, 1) == TEST_SUCCESS, "YCC to RGB conversion failed in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // RGB to YCC
  scalar_time = MEASURE(cspace_conversion(input_rgb, output, W, H, RGB2YCC));
  CHECK_TRUE(compare_tensors_uint8_with_error(input_ycc, output, N, H, W, C, 1) == TEST_SUCCESS, "RGB to YCC conversion failed in scalar implementation");
  rvv_time = MEASURE(cspace_conversion_rvv(input_rgb, output, W, H, RGB2YCC));
  CHECK_TRUE(compare_tensors_uint8_with_error(input_ycc, output, N, H, W, C, 1) == TEST_SUCCESS, "RGB to YCC conversion failed in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // YUV to RGB
  scalar_time = MEASURE(cspace_conversion(input_yuv, output, W, H, YUV2RGB));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_yuv, output, N, H, W, C, 1) == TEST_SUCCESS, "YUV to RGB conversion failed in scalar implementation");
  rvv_time = MEASURE(cspace_conversion_rvv(input_yuv, output, W, H, YUV2RGB));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_yuv, output, N, H, W, C, 1) == TEST_SUCCESS, "YUV to RGB conversion failed in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // RGB to YUV
  scalar_time = MEASURE(cspace_conversion(input_rgb, output, W, H, RGB2YUV));
  CHECK_TRUE(compare_tensors_uint8_with_error(input_yuv, output, N, H, W, C, 1) == TEST_SUCCESS, "RGB to YUV conversion failed in scalar implementation");
  rvv_time = MEASURE(cspace_conversion_rvv(input_rgb, output, W, H, RGB2YUV));
  CHECK_TRUE(compare_tensors_uint8_with_error(input_yuv, output, N, H, W, C, 1) == TEST_SUCCESS, "RGB to YUV conversion failed in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // YUV to Gray
  scalar_time = MEASURE(cspace_conversion(input_yuv, output, W, H, YUV2GRAY));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_gray, output, N, H, W, 1, 1) == TEST_SUCCESS, "YUV to Gray conversion failed in scalar implementation");
  rvv_time = MEASURE(cspace_conversion_rvv(input_yuv, output, W, H, YUV2GRAY));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_gray, output, N, H, W, 1, 1) == TEST_SUCCESS, "YUV to Gray conversion failed in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // RGB to Gray
  scalar_time = MEASURE(cspace_conversion(input_rgb, output, W, H, RGB2GRAY));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_gray, output, N, H, W, 1, 1) == TEST_SUCCESS, "RGB to Gray conversion failed in scalar implementation");
  rvv_time = MEASURE(cspace_conversion_rvv(input_rgb, output, W, H, RGB2GRAY));
  CHECK_TRUE(compare_tensors_uint8_with_error(golden_gray, output, N, H, W, 1, 1) == TEST_SUCCESS, "RGB to Gray conversion failed in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
