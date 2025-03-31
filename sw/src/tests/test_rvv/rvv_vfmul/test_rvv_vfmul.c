// Description: This program demonstrates the use of RISC-V vector intrinsics to load,
// multiply, and store a vector of floats. The results are then compared against expected values
// values to verify correctness.

#include <riscv_vector.h>
#include <testutils.h>

static float __attribute__((aligned(64), section(".l1"))) data[8] = {0., 1., 2., 3., 4., 5., 6., 7.};

void generate_expected_results(float *expected, float *data, size_t size, float multiplier) {
  float sum = 0.;
  for (size_t i = 0; i < size; i++) {
    sum += data[i];
    expected[i] = data[i] * multiplier;
  }

  // This checks makes sure that we actually fetched non-zero data from the l1
  ASSERT(sum > (float)0.);
}

int main() {
  testcase_init();

  // Generate expected results
  float expected[8];
  generate_expected_results(expected, data, 8, 1.5);

  // generate rvv results
  uint32_t     vl = __riscv_vsetvl_e32m1(sizeof(data) / sizeof(float));
  vfloat32m1_t v  = __riscv_vle32_v_f32m1(data, vl);
  v               = __riscv_vfmul_vf_f32m1(v, 1.5, vl);
  __riscv_vse32_v_f32m1(data, v, vl);

  // Check results
  int success = TEST_SUCCESS; // Flag to indicate if the test passes
  for (int i = 0; i < 8; i++) {
    if (data[i] != expected[i]) {
      success = TEST_FAILURE;
    }
  }
  CHECK_TRUE(success == TEST_SUCCESS, "Multiplication results do not match expected values");

  return testcase_finalize();
}
