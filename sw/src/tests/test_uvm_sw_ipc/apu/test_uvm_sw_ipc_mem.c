#include <printf.h>
#include <thread.h>
#include "../test_uvm_sw_ipc_common.h"
#include <multicore.h>
#include <testutils.h>

int main() {
  testcase_init();

  printf("starting test_uvm_sw_ipc_mem...\n");

  for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
    thread_launch(i, test_uvm_sw_ipc_mem, NULL);
  }
  CHECK_EQUAL_INT(0, test_uvm_sw_ipc_mem(NULL));
  CHECK_EQUAL_INT(0, thread_join_all());

  // Start all cores
  for(uint32_t i = AI_CORE_0; i < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER; i++) {
    start_core(i);
  }
  for(uint32_t i = PVE_0_CLUSTER_0_CORE_0; i < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER; i++) {
    start_core(i);
  }
  for(uint32_t i = PVE_1_CLUSTER_0_CORE_0; i < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER; i++) {
    start_core(i);
  }


  // Wait for all cores
  for(uint32_t i = AI_CORE_0; i < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER; i++) {
    CHECK_EQUAL_INT(0, wait_core(i));
  }
  for(uint32_t i = PVE_0_CLUSTER_0_CORE_0; i < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER; i++) {
    CHECK_EQUAL_INT(0, wait_core(i));
  }
  for(uint32_t i = PVE_1_CLUSTER_0_CORE_0; i < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER; i++) {
    CHECK_EQUAL_INT(0, wait_core(i));
  }

  return testcase_finalize();
}
