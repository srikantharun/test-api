#include <testutils.h>
#include <atomics.h>
#include <multicore.h>
#include <thread.h>
#include <test_atomics/atomic_helper.h>

int main() {
  testcase_init();
  /* START TEST */

#if HW_DEFINES_APU_CORE_NUMBER != 1
  enable_simple_multicore_printf(APU_CORE_5);
  for(tid_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id <= PVE_0_CLUSTER_3_CORE_1; core_id++) {
    start_core(core_id);
    CHECK_TRUE(wait_core(core_id) == TEST_SUCCESS);
  }
  disable_simple_multicore_printf(APU_CORE_5);

  // Test for correct return value.
  for (tid_t core_id = 1; core_id < HW_DEFINES_APU_CORE_NUMBER; core_id++) {
    thread_launch(core_id, test_atomic_helper, NULL);
    thread_join(core_id);
  }
#endif

  test_atomic_helper(NULL);

  /* END TEST */
  return testcase_finalize();
}

