// Description: Test application for gemm kernel
// This test program verifies the functionality of the gemm_i32_rvv kernel for matrix multiplication.
// The test multiplies matrices A and B, stores the result in matrix C, and compares it with a reference matrix ref.
// If the comparison fails, it indicates that the matrix multiplication did not produce the expected results.
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#include <stdint.h>
#include <string.h>
#include <gemm.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

extern const uint32_t M;
extern const uint32_t N;
extern const uint32_t P;

extern int32_t A[];
extern int32_t B[];
extern int32_t C[];
extern int32_t ref[];

int main() {
  uint64_t rvv_time;

  testcase_init();

  rvv_time = MEASURE(gemm_i32_rvv(M, N, P, A, B, C));
  CHECK_TRUE(compare_tensors_int32(ref, C, 1, 1, M, N) == TEST_SUCCESS, "Matrix multiplication result does not match reference");

  LOG_INF("> Execution took %lu cycles\n", rvv_time);

  return testcase_finalize();
}
