// Description:
// This program tests the implementation of the softmax kernel on a matrix
// using two different methods: a standard softmax and an RVV (RISC-V Vector)
// optimized version. The tests are performed on both the X and Y dimensions
// of the matrix to ensure correctness. The results are compared against
// precomputed golden reference tensors to verify the accuracy of the implementations.
//
// Steps:
// 1. Apply the standard softmax function on the matrix along the X dimension.
// 2. Compare the result against the golden reference tensor for the X dimension.
// 3. Apply the RVV optimized softmax function on the matrix along the X dimension.
// 4. Compare the result against the golden reference tensor for the X dimension.
// 5. TODO: Measure performance difference between the softmax implementations.
//
// 1. Apply the standard softmax function on the matrix along the Y dimension.
// 2. Compare the result against the golden reference tensor for the Y dimension.
// 3. Apply the RVV optimized softmax function on the matrix along the Y dimension.
// 4. Compare the result against the golden reference tensor for the Y dimension.
// 5. TODO: Measure performance difference between the softmax implementations.
//

#include <stdint.h>
#include <softmax.h>
#include <stdio.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

extern const uint32_t W;
extern const uint32_t H;

extern _Float16 matrix[];
extern _Float16 matrix_cpy[];
extern _Float16 golden_x[];
extern _Float16 golden_y[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  scalar_time = MEASURE(softmax(matrix, W, H, X_DIMENSION));
  CHECK_TRUE(compare_tensors_float16(golden_x, matrix, 1, H, W, 1) == TEST_SUCCESS, "Standard softmax X dimension mismatch");

  copy_tensor_float16(matrix_cpy, matrix, 1, H, W, 1);

  rvv_time = MEASURE(softmax_rvv(matrix, W, H, X_DIMENSION));
  CHECK_TRUE(compare_tensors_float16(golden_x, matrix, 1, H, W, 1) == TEST_SUCCESS, "RVV softmax X dimension mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  copy_tensor_float16(matrix_cpy, matrix, 1, H, W, 1);

  scalar_time = MEASURE(softmax(matrix, W, H, Y_DIMENSION));
  CHECK_TRUE(compare_tensors_float16(golden_y, matrix, 1, H, W, 1) == TEST_SUCCESS, "Standard softmax Y dimension mismatch");

  copy_tensor_float16(matrix_cpy, matrix, 1, H, W, 1);

  rvv_time = MEASURE(softmax_rvv(matrix, W, H, Y_DIMENSION));
  CHECK_TRUE(compare_tensors_float16(golden_y, matrix, 1, H, W, 1) == TEST_SUCCESS, "RVV softmax Y dimension mismatch");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
