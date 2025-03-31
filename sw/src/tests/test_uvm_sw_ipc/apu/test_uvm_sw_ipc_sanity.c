#include <testutils.h>
#include <thread.h>
#include <util.h>
#include <uvm_ipc/uvm_sw_ipc.h>
#include <multicore.h>
#include "../test_uvm_sw_ipc_common.h"

#ifdef SOC_PERIPH_SPIKE_SIMULATION
static const char *reg_path = "spike_top_tb.th.dummy_uvm_sw_ipc_hdl_test_reg";
#elif SYSTEM_TOP
static const char *reg_path = "sim_top.dummy_uvm_sw_ipc_hdl_test_reg";
#else
static const char *reg_path = "hdl_top.dummy_uvm_sw_ipc_hdl_test_reg";
#endif

int thread_hdl_test(void *arg) {
  UNUSED(arg);

  return test_uvm_sw_ipc_sanity_hdl(reg_path);
}

int main() {
  testcase_init();

  // HDL test: sequential as access to the same HDL register is shared
  CHECK_EQUAL_INT(0, thread_hdl_test(NULL));
  for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
    thread_launch(i, thread_hdl_test, NULL);
    CHECK_EQUAL_INT(0, thread_join(i));
  }

  // synchronization test: run in parallel
  uvm_sw_ipc_print_info(0, "test uvm_sw_ipc synchronization functions");
  for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
    thread_launch(i, test_uvm_sw_ipc_sanity_synchronization, NULL);
  }
  CHECK_EQUAL_INT(0, test_uvm_sw_ipc_sanity_synchronization(NULL));
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
