// Description: Test application for the crop_resize kernel
// This test program verifies the functionality of the crop_resize kernel using the RVV implementation.
// The test involves cropping and resizing an image and comparing the results against a golden reference image.
// The execution time in cycles is measured and logged for performance evaluation.

#include <stdint.h>
#include <string.h>
#include <crop_resize.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <encoding.h>
#include <log.h>

extern const uint32_t SRC_H;
extern const uint32_t SRC_W;
extern const uint32_t RSZ_H;
extern const uint32_t RSZ_W;
extern const uint32_t CRP_H;
extern const uint32_t CRP_W;
extern const uint32_t C;

extern uint8_t img_src[] __attribute__((aligned(4)));
extern uint8_t img_dst[] __attribute__((aligned(4)));
extern uint8_t img_ref[] __attribute__((aligned(4)));

int main() {
  uint64_t rvv_time;

  testcase_init();

  rvv_time = MEASURE(crop_resize_rvv(img_src, img_dst, SRC_H, SRC_W, C, RSZ_H, RSZ_W, CRP_H, CRP_W));

  CHECK_TRUE(compare_tensors_uint8_with_error(img_ref, img_dst, 1, CRP_H, CRP_W, C, 1) == TEST_SUCCESS, "Crop and resize kernel output does not match the golden reference image");

  LOG_INF("> Execution took %lu cycles\n", rvv_time);

  return testcase_finalize();
}
