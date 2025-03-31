// Description: Test application for the attention kernel
// This test program verifies the functionality of both scalar and RVV implementations.
// The test covers encoder-decoder attention and self-attention for different sequence lengths.
// The results are compared against golden references with an allowable error margin due to
// floating-point precision differences.

#include <stdint.h>
#include <attention.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <encoding.h>
#include <log.h>

// Constants
extern const uint32_t Nxh;
extern const uint32_t L0;
extern const uint32_t L1;
extern const uint32_t L2;
extern const uint32_t d_k;
extern const _Float16 inv_sqrt_d_k;

// Input matrices
extern _Float16 Q[];
extern _Float16 Q0self[];
extern _Float16 K0[];
extern _Float16 V0[];
extern _Float16 Q1self[];
extern _Float16 K1[];
extern _Float16 V1[];
extern _Float16 Q2self[];
extern _Float16 K2[];
extern _Float16 V2[];

// Buffer for intermediate QK matrix
extern _Float16 QK0[];
extern _Float16 QK1[];
extern _Float16 QK2[];

// Output matrix
extern _Float16 A0[];
extern _Float16 A1[];
extern _Float16 A2[];

// Golden references
extern _Float16 A0_golden[];
extern _Float16 A0self_golden[];
extern _Float16 A1_golden[];
extern _Float16 A1self_golden[];
extern _Float16 A2_golden[];
extern _Float16 A2self_golden[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;
  testcase_init();

  // Encoder-decoder attention
  LOG_INF("Running encoder-decoder attention for Nxh = %u, L = %u, d_k = %u\n", Nxh, L0, d_k);
  scalar_time = MEASURE(attention(Nxh, 1, L0, d_k, inv_sqrt_d_k, Q, K0, V0, QK0, A0));
  CHECK_TRUE(compare_tensors_float16(A0_golden, A0, 1, Nxh, d_k, 1) == TEST_SUCCESS, "Encoder-decoder attention failed for L0 in scalar implementation");
  rvv_time = MEASURE(attention_rvv(Nxh, 1, L0, d_k, inv_sqrt_d_k, Q, K0, V0, QK0, A0));
  CHECK_TRUE(compare_tensors_float16_with_error(A0_golden, A0, 1, Nxh, d_k, 1, 0.01f) == TEST_SUCCESS, "Encoder-decoder attention failed for L0 in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Self-attention
  LOG_INF("Running self-attention for Nxh = %u, L = %u, d_k = %u\n", Nxh, L0, d_k);
  scalar_time = MEASURE(attention(Nxh, L0, L0, d_k, inv_sqrt_d_k, Q0self, K0, V0, QK0, A0));
  CHECK_TRUE(compare_tensors_float16(A0self_golden, A0, 1, Nxh, d_k, L0) == TEST_SUCCESS, "Self-attention failed for L0 in scalar implementation");
  rvv_time = MEASURE(attention_rvv(Nxh, L0, L0, d_k, inv_sqrt_d_k, Q0self, K0, V0, QK0, A0));
  CHECK_TRUE(compare_tensors_float16_with_error(A0self_golden, A0, 1, Nxh, d_k, L0, 0.01f) == TEST_SUCCESS, "Self-attention failed for L0 in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Encoder-decoder attention
  LOG_INF("Running encoder-decoder attention for Nxh = %u, L = %u, d_k = %u\n", Nxh, L1, d_k);
  scalar_time =MEASURE(attention(Nxh, 1, L1, d_k, inv_sqrt_d_k, Q, K1, V1, QK1, A1));
  CHECK_TRUE(compare_tensors_float16(A1_golden, A1, 1, Nxh, d_k, 1) == TEST_SUCCESS, "Encoder-decoder attention failed for L1 in scalar implementation");
  rvv_time = MEASURE(attention_rvv(Nxh, 1, L1, d_k, inv_sqrt_d_k, Q, K1, V1, QK1, A1));
  CHECK_TRUE(compare_tensors_float16_with_error(A1_golden, A1, 1, Nxh, d_k, 1, 0.01f) == TEST_SUCCESS, "Encoder-decoder attention failed for L1 in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Self-attention
  LOG_INF("Running self-attention for Nxh = %u, L = %u, d_k = %u\n", Nxh, L1, d_k);
  scalar_time = MEASURE(attention(Nxh, L1, L1, d_k, inv_sqrt_d_k, Q1self, K1, V1, QK1, A1));
  CHECK_TRUE(compare_tensors_float16(A1self_golden, A1, 1, Nxh, d_k, L1) == TEST_SUCCESS, "Self-attention failed for L1 in scalar implementation");
  rvv_time = MEASURE(attention_rvv(Nxh, L1, L1, d_k, inv_sqrt_d_k, Q1self, K1, V1, QK1, A1));
  CHECK_TRUE(compare_tensors_float16_with_error(A1self_golden, A1, 1, Nxh, d_k, L1, 0.01f) == TEST_SUCCESS, "Self-attention failed for L1 in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Encoder-decoder attention
  LOG_INF("Running encoder-decoder attention for Nxh = %u, L = %u, d_k = %u\n", Nxh, L2, d_k);
  scalar_time = MEASURE(attention(Nxh, 1, L2, d_k, inv_sqrt_d_k, Q, K2, V2, QK2, A2));
  CHECK_TRUE(compare_tensors_float16(A2_golden, A2, 1, Nxh, d_k, 1) == TEST_SUCCESS, "Encoder-decoder attention failed for L2 in scalar implementation");
  rvv_time = MEASURE(attention_rvv(Nxh, 1, L2, d_k, inv_sqrt_d_k, Q, K2, V2, QK2, A2));
  CHECK_TRUE(compare_tensors_float16_with_error(A2_golden, A2, 1, Nxh, d_k, 1, 0.01f) == TEST_SUCCESS, "Encoder-decoder attention failed for L2 in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Self-attention
  LOG_INF("Running self-attention for Nxh = %u, L = %u, d_k = %u\n", Nxh, L2, d_k);
  scalar_time = MEASURE(attention(Nxh, L2, L2, d_k, inv_sqrt_d_k, Q2self, K2, V2, QK2, A2));
  CHECK_TRUE(compare_tensors_float16(A2self_golden, A2, 1, Nxh, d_k, L2) == TEST_SUCCESS, "Self-attention failed for L2 in scalar implementation");
  rvv_time = MEASURE(attention_rvv(Nxh, L2, L2, d_k, inv_sqrt_d_k, Q2self, K2, V2, QK2, A2));
  CHECK_TRUE(compare_tensors_float16_with_error(A2self_golden, A2, 1, Nxh, d_k, L2, 0.01f) == TEST_SUCCESS, "Self-attention failed for L2 in RVV implementation");
  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
