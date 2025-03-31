#include <asm.h>
#include <printf.h>
#include <thread.h>
#include <util.h>
#include <testutils.h>
#include <multicore.h>
#include <uvm_ipc/uvm_sw_ipc.h>

#include "../test_uvm_sw_ipc_common.h"

int thread_print(void *arg) {
    UNUSED(arg);

    uint64_t hartid = r_mhartid();
    // stress the UVM SW IPC interface
    for (int i = 0; i < 16; i++) {
        printf("Hello from core %d!\n", hartid);
    }

    return 0;
}

int main() {

  testcase_init();

  CHECK_EQUAL_INT(0, test_uvm_sw_ipc_printf());

  // Test for correct return value.
  for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
      thread_launch(i, thread_print, NULL);
  }

  for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
      thread_join(i);
  }

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
