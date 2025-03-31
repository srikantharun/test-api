// Description:
// This program tests the implementation of the Swish activation function
// on a tensor using two different methods: a standard implementation and
// an RVV (RISC-V Vector) optimized version. The results are compared
// against precomputed golden reference tensors to verify the accuracy
// of the implementations.
//
// Steps:
// 1. Apply the standard Swish function on the tensor.
// 2. Compare the result against the golden reference tensor.
// 3. Apply the RVV optimized Swish function on the tensor copy.
// 4. Compare the result against the golden reference tensor.
//

#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <swish.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

extern const uint32_t N;
extern const uint32_t W;
extern const uint32_t H;
extern const uint32_t C;

extern _Float16 tensor[];
extern _Float16 tensor_cpy[];
extern _Float16 golden[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  scalar_time = MEASURE(swish(tensor, N, W, H, C));
  CHECK_TRUE(compare_tensors_float16(golden, tensor, N, H, W, C) == TEST_SUCCESS, "Swish activation (standard) failed");

  rvv_time = MEASURE(swish_rvv(tensor_cpy, N, W, H, C));
  CHECK_TRUE(compare_tensors_float16(golden, tensor_cpy, N, H, W, C) == TEST_SUCCESS, "Swish activation (RVV) failed");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
