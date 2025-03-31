// Description: Test application for conv2d kernels
// This test program verifies the functionality of various 2D convolution kernels,
// including 3x3 and 7x7 filters, as well as int8 and int32 data types. The test
// compares the outputs of standard and optimized versions of the convolution kernels
// against golden reference values to ensure correctness.

#include <stdint.h>
#include <conv2d.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

// Matrix and filter size constants
extern const int32_t W;
extern const int32_t H;
extern const int32_t F3;
extern const int32_t F7;

// Filter matrix
extern int32_t filter3[];
extern int8_t  filter3_i8[];
extern int32_t filter7[];
extern int8_t  filter7_i8[];

// Input image
extern int32_t image3[];
extern int8_t  image3_i8[];
extern int32_t image7[];
extern int8_t  image7_i8[];

// Output
extern int32_t output[];
extern int8_t  output_i8[];

// Golden model
extern int32_t golden_3x3[];
extern int8_t  golden_3x3_i8[];
extern int32_t golden_7x7[];
extern int8_t  golden_7x7_i8[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  scalar_time = MEASURE(conv2d(image3, H, W, filter3, F3, output));
  CHECK_TRUE(compare_tensors_int32(golden_3x3, output, 1, H, W, 1) == TEST_SUCCESS, "conv2d 3x3 int32 test failed");
  rvv_time = MEASURE(conv2d_3x3(output, image3, filter3, H, W));
  CHECK_TRUE(compare_tensors_int32(golden_3x3, output, 1, H, W, 1) == TEST_SUCCESS, "conv2d_3x3 int32 test failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(conv2d(image7, H, W, filter7, F7, output));
  CHECK_TRUE(compare_tensors_int32(golden_7x7, output, 1, H, W, 1) == TEST_SUCCESS, "conv2d 7x7 int32 test failed");
  rvv_time = MEASURE(conv2d_7x7(output, image7, filter7, H, W));
  CHECK_TRUE(compare_tensors_int32(golden_7x7, output, 1, H, W, 1) == TEST_SUCCESS, "conv2d_7x7 int32 test failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(conv2d_i8(image3_i8, H, W, filter3_i8, F3, output_i8));
  CHECK_TRUE(compare_tensors_int8(golden_3x3_i8, output_i8, 1, H, W, 1) == TEST_SUCCESS, "conv2d 3x3 int8 test failed");
  rvv_time = MEASURE(conv2d_3x3_i8(output_i8, image3_i8, filter3_i8, H, W));
  CHECK_TRUE(compare_tensors_int8(golden_3x3_i8, output_i8, 1, H, W, 1) == TEST_SUCCESS, "conv2d_3x3 int8 test failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(conv2d_i8(image7_i8, H, W, filter7_i8, F7, output_i8));
  CHECK_TRUE(compare_tensors_int8(golden_7x7_i8, output_i8, 1, H, W, 1) == TEST_SUCCESS, "conv2d 7x7 int8 test failed");
  rvv_time = MEASURE(conv2d_7x7_i8(output_i8, image7_i8, filter7_i8, H, W));
  CHECK_TRUE(compare_tensors_int8(golden_7x7_i8, output_i8, 1, H, W, 1) == TEST_SUCCESS, "conv2d_7x7 int8 test failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
