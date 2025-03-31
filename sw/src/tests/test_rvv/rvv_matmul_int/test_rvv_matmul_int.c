// Description: Test application for integer matmul kernel
// This test program performs matrix multiplication on both int32 and int8 data types
// using various implementations. It verifies the correctness of each multiplication
// by comparing the results against precomputed golden matrices.
//
// The test consists of the following steps:
// 1. Perform matrix multiplication on int32 data using the basic implementation and compare the results.
// 2. Perform matrix multiplication on int32 data using the RVV (RISC-V Vector) implementation and compare the results.
// 3. Perform matrix multiplication on int32 data using the RVV 2xVL, 4xVL, and 8xVL implementations and compare the results.
// 4. Perform matrix multiplication on int8 data using the basic implementation and compare the results.
// 5. Perform matrix multiplication on int8 data using the RVV implementation and compare the results.
// 6. Perform matrix multiplication on int8 data using the RVV 2xVL, 4xVL, and 8xVL implementations and compare the results.
//

#include <stdint.h>
#include <matmul_int.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

extern const uint32_t M;
extern const uint32_t N;
extern const uint32_t P;

extern int32_t matrix_A_i32[];
extern int32_t matrix_B_i32[];
extern int32_t output_C_i32[];
extern int32_t golden_matrix_i32[];
extern int8_t  matrix_A_i8[];
extern int8_t  matrix_B_i8[];
extern int8_t  output_C_i8[];
extern int8_t  golden_matrix_i8[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // int32
  scalar_time = MEASURE(matmul_i32(matrix_A_i32, matrix_B_i32, output_C_i32, M, N, P));
  CHECK_TRUE(compare_tensors_int32(golden_matrix_i32, output_C_i32, 1, M, P, 1) == TEST_SUCCESS, "matmul_i32: Result mismatch");
  rvv_time = MEASURE(matmul_rvv_i32(output_C_i32, matrix_A_i32, matrix_B_i32, M, N, P));
  CHECK_TRUE(compare_tensors_int32(golden_matrix_i32, output_C_i32, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i32: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_i32_2xVL(output_C_i32, matrix_A_i32, matrix_B_i32, M, N, P));
  CHECK_TRUE(compare_tensors_int32(golden_matrix_i32, output_C_i32, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i32_2xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_i32_4xVL(output_C_i32, matrix_A_i32, matrix_B_i32, M, N, P));
  CHECK_TRUE(compare_tensors_int32(golden_matrix_i32, output_C_i32, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i32_4xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_i32_8xVL(output_C_i32, matrix_A_i32, matrix_B_i32, M, N, P));
  CHECK_TRUE(compare_tensors_int32(golden_matrix_i32, output_C_i32, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i32_8xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // int8
  scalar_time = MEASURE(matmul_i8(matrix_A_i8, matrix_B_i8, output_C_i8, M, N, P));
  CHECK_TRUE(compare_tensors_int8(golden_matrix_i8, output_C_i8, 1, M, P, 1) == TEST_SUCCESS, "matmul_i8: Result mismatch");

  rvv_time = MEASURE(matmul_rvv_i8(output_C_i8, matrix_A_i8, matrix_B_i8, M, N, P));
  CHECK_TRUE(compare_tensors_int8(golden_matrix_i8, output_C_i8, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i8: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_i8_2xVL(output_C_i8, matrix_A_i8, matrix_B_i8, M, N, P));
  CHECK_TRUE(compare_tensors_int8(golden_matrix_i8, output_C_i8, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i8_2xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_i8_4xVL(output_C_i8, matrix_A_i8, matrix_B_i8, M, N, P));
  CHECK_TRUE(compare_tensors_int8(golden_matrix_i8, output_C_i8, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i8_4xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  rvv_time = MEASURE(matmul_rvv_i8_8xVL(output_C_i8, matrix_A_i8, matrix_B_i8, M, N, P));
  CHECK_TRUE(compare_tensors_int8(golden_matrix_i8, output_C_i8, 1, M, P, 1) == TEST_SUCCESS, "matmul_rvv_i8_8xVL: Result mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
