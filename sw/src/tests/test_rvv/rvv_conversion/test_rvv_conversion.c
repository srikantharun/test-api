// Description: Test application for tensor conversion kernels.
// This test verifies the functionality of various tensor conversion
// functions, including conversions between different data types
// (int8, uint8, float16) and different tensor formats (NCHW and NHWC).
// It also compares the output of standard and vectorized versions of
// these functions to ensure correctness.

#include <stdint.h>
#include <conversion.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

#define SEED_A 0
#define SEED_B 1
#define SEED_C 16
#define SEED_D 5
#define SEED_E 32

#define SEED_Af 0
#define SEED_Bf 1.1
#define SEED_Cf 16.256
#define SEED_Df 5.12
#define SEED_Ef -32.035

#define N 1
#define W 16
#define H 16
#define C 3

int8_t __attribute__((aligned(64), section(".l1"))) Si[N * W * H * C];
uint8_t __attribute__((aligned(64), section(".l1"))) Su[N * W * H * C];
_Float16 __attribute__((aligned(64), section(".l1"))) Sf[N * W * H * C];
_Float16 __attribute__((aligned(64), section(".l1"))) Df[N * W * H * C];
_Float16 __attribute__((aligned(64), section(".l1"))) Df_RVV[N * W * H * C];
int8_t __attribute__((aligned(64), section(".l1"))) Di[N * W * H * C];
int8_t __attribute__((aligned(64), section(".l1"))) Di_RVV[N * H * W * C];
uint8_t __attribute__((aligned(64), section(".l1"))) Du[N * W * H * C];
uint8_t __attribute__((aligned(64), section(".l1"))) Du_RVV[N * H * W * C];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  init_tensor_int8(Si, N, H, W, C, SEED_A, SEED_B, SEED_C, SEED_D, -SEED_E, TENSOR_FORMAT_NCHW);
  init_tensor_uint8(Su, N, H, W, C, SEED_A, SEED_B, SEED_C, SEED_D, SEED_E, TENSOR_FORMAT_NCHW);
  init_tensor_float16(Sf, N, H, W, C, SEED_Af, SEED_Bf, SEED_Cf, SEED_Df, SEED_Ef, TENSOR_FORMAT_NCHW);

  // uint8 -> float16 conversion
  scalar_time = MEASURE(tensor_uint8_to_float16(Su, Df, N, W, H, C));
  rvv_time = MEASURE(tensor_uint8_to_float16_rvv(Su, Df_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_float16(Df, Df_RVV, N, H, W, C) == TEST_SUCCESS, "uint8 to float16 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(tensor_uint8_to_float16_scaled(Su, Df, N, W, H, C));
  rvv_time = MEASURE(tensor_uint8_to_float16_scaled_rvv(Su, Df_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_float16(Df, Df_RVV, N, H, W, C) == TEST_SUCCESS, "Scaled uint8 to float16 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // float16 -> int8 conversion
  scalar_time = MEASURE(tensor_float16_to_int8(Sf, Di, N, W, H, C));
  rvv_time = MEASURE(tensor_float16_to_int8_rvv(Sf, Di_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_int8(Di, Di_RVV, N, H, W, C) == TEST_SUCCESS, "float16 to int8 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Tensor format NCHW to NHWC conversion
  scalar_time = MEASURE(tensor_format_nchw_to_nhwc_float16(Sf, Df, N, W, H, C));
  rvv_time = MEASURE(tensor_format_nchw_to_nhwc_float16_rvv(Sf, Df_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_float16(Df, Df_RVV, N, H, W, C) == TEST_SUCCESS, "Tensor format NCHW to NHWC float16 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(tensor_format_nchw_to_nhwc_uint8(Su, Du, N, W, H, C));
  rvv_time = MEASURE(tensor_format_nchw_to_nhwc_uint8_rvv(Su, Du_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_uint8(Du, Du_RVV, N, H, W, C) == TEST_SUCCESS, "Tensor format NCHW to NHWC uint8 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(tensor_format_nchw_to_nhwc_int8(Si, Di, N, W, H, C));
  rvv_time = MEASURE(tensor_format_nchw_to_nhwc_int8_rvv(Si, Di_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_int8(Di, Di_RVV, N, H, W, C) == TEST_SUCCESS, "Tensor format NCHW to NHWC int8 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Tensor format NHWC to NCHW conversion
  scalar_time = MEASURE(tensor_format_nhwc_to_nchw_float16(Sf, Df, N, W, H, C));
  rvv_time = MEASURE(tensor_format_nhwc_to_nchw_float16_rvv(Sf, Df_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_float16(Df, Df_RVV, N, H, W, C) == TEST_SUCCESS, "Tensor format NHWC to NCHW float16 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(tensor_format_nhwc_to_nchw_int8(Si, Di, N, W, H, C));
  rvv_time = MEASURE(tensor_format_nhwc_to_nchw_int8_rvv(Si, Di_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_int8(Di, Di_RVV, N, H, W, C) == TEST_SUCCESS, "Tensor format NHWC to NCHW int8 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  scalar_time = MEASURE(tensor_format_nhwc_to_nchw_uint8(Su, Du, N, W, H, C));
  rvv_time = MEASURE(tensor_format_nhwc_to_nchw_uint8_rvv(Su, Du_RVV, N, W, H, C));
  CHECK_TRUE(compare_tensors_uint8(Du, Du_RVV, N, H, W, C) == TEST_SUCCESS, "Tensor format NHWC to NCHW uint8 conversion failed");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
