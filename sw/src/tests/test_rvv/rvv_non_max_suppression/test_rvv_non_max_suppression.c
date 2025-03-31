// Description:
// This test application evaluates the non_max_suppression kernel using two implementations:
// a standard version and an RVV (RISC-V Vector) optimized version. The test verifies the
// correctness of the implementations by comparing the results against precomputed golden
// reference indices. The test also sorts the resulting indices and compares them to ensure
// they match the golden reference. The performance difference between the two implementations
// is intended to be measured in future enhancements.
//

#include <non_max_suppression.h>
#include <printf.h>
#include <tensor_op.h>
#include <testutils.h>
#include <log.h>

#define SORT(ARRAY, NUM)                  \
  ({                                      \
    for (uint32_t i = 0; i < NUM; i++) {       \
      for (uint32_t j = i + 1; j < NUM; j++) { \
        if (ARRAY[i] > ARRAY[j]) {        \
          uint32_t tmp = ARRAY[i];        \
          ARRAY[i]     = ARRAY[j];        \
          ARRAY[j]     = tmp;             \
        }                                 \
      }                                   \
    }                                     \
  })

extern const uint32_t num_boxes;

extern int32_t  boxes[] __attribute__((aligned(4)));
extern uint32_t classes[] __attribute__((aligned(4)));
extern _Float16 scores[] __attribute__((aligned(4)));

extern const _Float16 score_threshold;
extern const _Float16 nms_threshold;

extern const uint32_t num_golden_indices;
extern uint32_t       golden_indices[] __attribute__((aligned(4)));

int main() {
  uint32_t nms_indices[num_boxes];
  uint32_t num_nms_indices;
  uint64_t scalar_time;
  uint64_t rvv_time;

  testcase_init();

  scalar_time = MEASURE({num_nms_indices = non_max_suppression(boxes, num_boxes, classes, scores, score_threshold, nms_threshold, nms_indices);});
  CHECK_TRUE(num_golden_indices == num_nms_indices, "Number of NMS indices does not match the golden reference");
  SORT(nms_indices, num_nms_indices);
  CHECK_TRUE(compare_tensors_uint32(golden_indices, nms_indices, 1, 1, num_golden_indices, 1) == TEST_SUCCESS, "NMS indices do not match the golden reference");


  rvv_time = MEASURE({num_nms_indices = non_max_suppression_rvv(boxes, num_boxes, classes, scores, score_threshold, nms_threshold, nms_indices);});
  CHECK_TRUE(num_golden_indices == num_nms_indices, "Number of RVV NMS indices does not match the golden reference");
  SORT(nms_indices, num_nms_indices);
  CHECK_TRUE(compare_tensors_uint32(golden_indices, nms_indices, 1, 1, num_golden_indices, 1) == TEST_SUCCESS, "RVV NMS indices do not match the golden reference");

  LOG_INF("> Speedup of %lux (%lu cycles -> %lu cycles)\n", (scalar_time / rvv_time), rvv_time, scalar_time);

  return testcase_finalize();
}
