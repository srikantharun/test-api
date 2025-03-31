// Description: Test application for AI core layer_norm kernel.
// This test program verifies the functionality of the layer normalization kernel using various test cases.
// Each test case involves normalizing the input data tensor with given scale and bias tensors, and comparing the results
// against golden reference tensors. The execution time in cycles is measured and logged for performance evaluation.

#include <stdint.h>
#include <printf.h>
#include <kernel_aic_layernorm.h>
#include <tensor_op.h>
#include <testutils.h>
#include <encoding.h>
#include <log.h>

extern const char *testcase_names[];
extern int         first_axis[];
extern DLTensor   *data_tensors[];
extern DLTensor   *scale_tensors[];
extern DLTensor   *bias_tensors[];
extern DLTensor   *golden_tensors[];

int main() {
  uint64_t rvv_time;
  uint32_t testcase;

  testcase_init();

  for (testcase = 0; testcase_names[testcase] != NULL; testcase++) {
    printf("Executing testcase %d (%s)\n", testcase + 1, testcase_names[testcase]);

    rvv_time = MEASURE(kernel_aic_layernorm_fp(data_tensors[testcase], data_tensors[testcase], scale_tensors[testcase], bias_tensors[testcase], first_axis[testcase], 1.0E-5f));

    CHECK_TRUE(compare_dltensors_with_error(golden_tensors[testcase], data_tensors[testcase], .01f) == TEST_SUCCESS, "Layer normalization failed for testcase %d (%s)", testcase + 1, testcase_names[testcase]);
    LOG_INF("Testcase #%d (%s):\n> Execution took %lu cycles\n", testcase + 1, testcase_names[testcase], rvv_time);
  }

  return testcase_finalize();
}
