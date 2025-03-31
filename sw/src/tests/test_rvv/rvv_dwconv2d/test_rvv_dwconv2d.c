// Description: Test application for dwconv2d kernel
// This test program verifies the correctness of depthwise convolution (dwconv2d) kernel
// implementations using both FP16 and FP32 precision with scalar and RVV optimizations.
// The output tensors are compared against golden reference tensors.

#include <stdint.h>
#include <dwconv2d.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

// Matrix and filter size constants
extern const int32_t N;
extern const int32_t C;
extern const int32_t H;
extern const int32_t W;
extern const int32_t F;

// Requantisation factors
extern float    a32[];
extern float    b32[];
extern _Float16 a16[];
extern _Float16 b16[];
extern int32_t  q[];

// dwconv2d input, output, and golden
extern int8_t image[];
extern int8_t filters[];
extern int8_t output[];
extern int8_t golden_fp16[];
extern int8_t golden_fp32[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // FP16 depthwise convolution
  scalar_time = MEASURE(dwconv2d_fp16(image, N, H, W, C, filters, F, output, a16, b16, q));
  // we should not check  _with_error function but we get rounding errors between the 2 arrays
  CHECK_TRUE(compare_tensors_int8_with_error(golden_fp16, output, N, H - F + 1, W - F + 1, C, 1) == TEST_SUCCESS, "FP16 scalar depthwise convolution output does not match the golden reference");
  rvv_time = MEASURE(dwconv2d_fp16_rvv(image, N, H, W, C, filters, F, output, a16, b16, q));
  CHECK_TRUE(compare_tensors_int8(golden_fp16, output, N, H - F + 1, W - F + 1, C) == TEST_SUCCESS, "FP16 RVV depthwise convolution output does not match the golden reference");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // FP32 depthwise convolution
  scalar_time = MEASURE(dwconv2d_fp32(image, N, H, W, C, filters, F, output, a32, b32));
  CHECK_TRUE(compare_tensors_int8(golden_fp32, output, N, H - F + 1, W - F + 1, C) == TEST_SUCCESS, "FP32 scalar depthwise convolution output does not match the golden reference");
  rvv_time = MEASURE(dwconv2d_fp32_rvv(image, N, H, W, C, filters, F, output, a32, b32));
  CHECK_TRUE(compare_tensors_int8(golden_fp32, output, N, H - F + 1, W - F + 1, C) == TEST_SUCCESS, "FP32 RVV depthwise convolution output does not match the golden reference");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
