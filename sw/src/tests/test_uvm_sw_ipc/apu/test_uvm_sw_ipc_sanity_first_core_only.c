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

  // synchronization test: run in parallel
  uvm_sw_ipc_print_info(0, "test uvm_sw_ipc synchronization functions");

  CHECK_EQUAL_INT(0, test_uvm_sw_ipc_sanity_synchronization(NULL));

  // Start all cores
  if (HW_DEFINES_AICORE_MODULE_NUMBER) {
    start_core(AI_CORE_0);
  }

  if (HW_DEFINES_PVE_0_CORE_NUMBER) {
    start_core(PVE_0_CLUSTER_0_CORE_0);
  }

  if (HW_DEFINES_PVE_1_CORE_NUMBER) {
    start_core(PVE_1_CLUSTER_0_CORE_0);
  }

  // Wait for all cores
  if (HW_DEFINES_AICORE_MODULE_NUMBER) {
    CHECK_EQUAL_INT(0, wait_core(AI_CORE_0));
  }

  if (HW_DEFINES_PVE_0_CORE_NUMBER) {
    CHECK_EQUAL_INT(0, wait_core(PVE_0_CLUSTER_0_CORE_0));
  }

  if (HW_DEFINES_PVE_1_CORE_NUMBER) {
    CHECK_EQUAL_INT(0, wait_core(PVE_1_CLUSTER_0_CORE_0));
  }

  return testcase_finalize();
}
