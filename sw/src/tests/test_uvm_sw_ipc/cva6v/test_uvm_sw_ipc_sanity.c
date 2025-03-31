#include <testutils.h>
#include "../test_uvm_sw_ipc_common.h"

#if SYSTEM_TOP
static const char *reg_path = "sim_top.dummy_uvm_sw_ipc_hdl_test_reg";
#else
static const char *reg_path = "hdl_top.dummy_uvm_sw_ipc_hdl_test_reg";
#endif

int main() {
  testcase_init();
  CHECK_EQUAL_INT(0, test_uvm_sw_ipc_sanity_hdl(reg_path));
  CHECK_EQUAL_INT(0, test_uvm_sw_ipc_sanity_synchronization(NULL));
  return testcase_finalize();
}
