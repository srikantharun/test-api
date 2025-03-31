// Description: Test application for floating-point matmul kernel
// This test program performs matrix multiplication on both float32 and float16 data types
// using various implementations. It verifies the correctness of each multiplication
// by comparing the results against precomputed golden matrices with an allowable error
// percentage.
//
// The test consists of the following steps:
// 1. Perform matrix multiplication on float32 data using the basic implementation and compare the results.
// 2. Perform matrix multiplication on float32 data using the RVV (RISC-V Vector) implementation and compare the results.
// 3. Perform matrix multiplication on float32 data using the RVV 2xVL, 4xVL, and 8xVL implementations and compare the results.
// 4. Perform matrix multiplication on float16 data using the basic implementation and compare the results.
// 5. Perform matrix multiplication on float16 data using the RVV implementation and compare the results.
// 6. Perform matrix multiplication on float16 data using the RVV 2xVL, 4xVL, and 8xVL implementations and compare the results.
//

#include <stdint.h>
#include <matmul_float.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

extern const uint32_t M;
extern const uint32_t N;
extern const uint32_t P;

extern float    matrix_A_f32[];
extern float    matrix_B_f32[];
extern float    output_C_f32[];
extern float    golden_matrix_f32[];
extern _Float16 matrix_A_f16[];
extern _Float16 matrix_B_f16[];
extern _Float16 output_C_f16[];
extern _Float16 golden_matrix_f16[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // float
  scalar_time = MEASURE(matmul_f32(matrix_A_f32, matrix_B_f32, output_C_f32, M, N, P));
  CHECK_TRUE(compare_tensors_float_with_error_percentage(golden_matrix_f32, output_C_f32, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_f32: Result mismatch");

  rvv_time = MEASURE(matmul_rvv_f32(output_C_f32, matrix_A_f32, matrix_B_f32, M, N, P));
  CHECK_TRUE(compare_tensors_float_with_error_percentage(golden_matrix_f32, output_C_f32, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f32: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_f32_2xVL(output_C_f32, matrix_A_f32, matrix_B_f32, M, N, P));
  CHECK_TRUE(compare_tensors_float_with_error_percentage(golden_matrix_f32, output_C_f32, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f32_2xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_f32_4xVL(output_C_f32, matrix_A_f32, matrix_B_f32, M, N, P));
  CHECK_TRUE(compare_tensors_float_with_error_percentage(golden_matrix_f32, output_C_f32, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f32_4xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_f32_8xVL(output_C_f32, matrix_A_f32, matrix_B_f32, M, N, P));
  CHECK_TRUE(compare_tensors_float_with_error_percentage(golden_matrix_f32, output_C_f32, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f32_8xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // float16
  scalar_time = MEASURE(matmul_f16(matrix_A_f16, matrix_B_f16, output_C_f16, M, N, P));
  CHECK_TRUE(compare_tensors_float16_with_error_percentage(golden_matrix_f16, output_C_f16, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_f16: Result mismatch");

  rvv_time = MEASURE(matmul_rvv_f16(output_C_f16, matrix_A_f16, matrix_B_f16, M, N, P));
  CHECK_TRUE(compare_tensors_float16_with_error_percentage(golden_matrix_f16, output_C_f16, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f16: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_f16_2xVL(output_C_f16, matrix_A_f16, matrix_B_f16, M, N, P));
  CHECK_TRUE(compare_tensors_float16_with_error_percentage(golden_matrix_f16, output_C_f16, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f16_2xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_f16_4xVL(output_C_f16, matrix_A_f16, matrix_B_f16, M, N, P));
  CHECK_TRUE(compare_tensors_float16_with_error_percentage(golden_matrix_f16, output_C_f16, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f16_4xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_f16_8xVL(output_C_f16, matrix_A_f16, matrix_B_f16, M, N, P));
  CHECK_TRUE(compare_tensors_float16_with_error_percentage(golden_matrix_f16, output_C_f16, 1, M, P, 1, 0.01f) == TEST_SUCCESS, "matmul_rvv_f16_8xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
