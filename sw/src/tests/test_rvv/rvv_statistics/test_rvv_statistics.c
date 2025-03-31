// Description: Test application for validating and comparing statistics kernels.
//              This test includes both standard and RISC-V Vector Extension (RVV)
//              implementations. The test validates correctness by comparing the results
//              with precomputed golden reference tensors and measures performance differences.
//
// Steps:
// 1a. Performs batch normalization using standard functions, validates against golden reference.
// 1b. Performs batch normalization using RVV functions, validates with an error margin.
//
// 2a. Performs layer normalization using standard functions, validates against golden reference.
// 2b. Performs layer normalization using RVV functions, validates with an error margin.
//
// 3a. Performs instance normalization using standard functions, validates against golden reference.
// 3b. Performs instance normalization using RVV functions, validates with an error margin.
//
// Parameters:
// - N: Batch size, in this case 2.
// - W: Width of the input tensor, in this case 16.
// - H: Height of the input tensor, in this case 16.
// - C: Number of channels in the input tensor, in this case 8.

#include <statistics.h>
#include <stdint.h>
#include <stdio.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

extern const uint32_t W;
extern const uint32_t H;
extern const uint32_t C;
extern const uint32_t N;

extern _Float16 tensor[];
extern _Float16 golden_batch[];
extern _Float16 golden_layer[];
extern _Float16 golden_instance[];

extern _Float16 _tensor[];
extern _Float16 STD[];
extern _Float16 MEAN[];

int main() {
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  // Batch Norm
  copy_tensor_float16(tensor, _tensor, N, H, W, C);

  scalar_time = MEASURE(({
    mean(_tensor, N, W, H, C, MEAN, NORM_BATCH);
    std(_tensor, N, W, H, C, MEAN, STD, NORM_BATCH);
    batch_norm(_tensor, N, W, H, C, MEAN, STD);
  }));

  CHECK_TRUE(compare_tensors_float16(golden_batch, _tensor, N, H, W, C) == TEST_SUCCESS, "Batch normalization (standard) failed");

  copy_tensor_float16(tensor, _tensor, N, H, W, C);

  rvv_time = MEASURE(({
    mean_rvv(_tensor, N, W, H, C, MEAN, NORM_BATCH);
    std_rvv(_tensor, N, W, H, C, MEAN, STD, NORM_BATCH);
    batch_norm_rvv(_tensor, N, W, H, C, MEAN, STD);
  }));

  CHECK_TRUE(compare_tensors_float16_with_error(golden_batch, _tensor, N, H, W, C, 0.1f) == TEST_SUCCESS, "Batch normalization (RVV) failed");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // Layer Norm
  copy_tensor_float16(tensor, _tensor, N, H, W, C);

  scalar_time = MEASURE(({
    mean(_tensor, N, W, H, C, MEAN, NORM_LAYER);
    std(_tensor, N, W, H, C, MEAN, STD, NORM_LAYER);
    layer_norm(_tensor, N, W, H, C, MEAN, STD);
  }));

  CHECK_TRUE(compare_tensors_float16(golden_layer, _tensor, N, H, W, C) == TEST_SUCCESS, "Layer normalization (standard) failed");

  copy_tensor_float16(tensor, _tensor, N, H, W, C);

  rvv_time = MEASURE(({
    mean_rvv(_tensor, N, W, H, C, MEAN, NORM_LAYER);
    std_rvv(_tensor, N, W, H, C, MEAN, STD, NORM_LAYER);
    layer_norm_rvv(_tensor, N, W, H, C, MEAN, STD);
  }));

  CHECK_TRUE(compare_tensors_float16_with_error(golden_layer, _tensor, N, H, W, C, 0.1f) == TEST_SUCCESS, "Layer normalization (RVV) failed");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  // // Instance Norm
  copy_tensor_float16(tensor, _tensor, N, H, W, C);

  scalar_time = MEASURE(({
    mean(_tensor, N, W, H, C, MEAN, NORM_INSTANCE);
    std(_tensor, N, W, H, C, MEAN, STD, NORM_INSTANCE);
    instance_norm(_tensor, N, W, H, C, MEAN, STD);
  }));

  CHECK_TRUE(compare_tensors_float16(golden_instance, _tensor, N, H, W, C) == TEST_SUCCESS, "Instance normalization (standard) failed");

  copy_tensor_float16(tensor, _tensor, N, H, W, C);

  rvv_time = MEASURE(({
    mean_rvv(_tensor, N, W, H, C, MEAN, NORM_INSTANCE);
    std_rvv(_tensor, N, W, H, C, MEAN, STD, NORM_INSTANCE);
    instance_norm_rvv(_tensor, N, W, H, C, MEAN, STD);
  }));

  CHECK_TRUE(compare_tensors_float16_with_error(golden_instance, _tensor, N, H, W, C, 0.1f) == TEST_SUCCESS, "Instance normalization (RVV) failed");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
