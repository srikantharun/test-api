#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <printf.h>

int main() {
  printf("Testing AiCORE l1 backdoor loading\r\n");

  enable_simple_multicore_printf(APU_CORE_5);

  for(uint32_t i = AI_CORE_0; i < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER; i++) {
    start_core(i);
  }

  for(uint32_t i = AI_CORE_0; i < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER; i++) {
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(i));
  }

  disable_simple_multicore_printf(APU_CORE_5);

  printf("Comparison finished!\r\n");

  /* END TEST */
  return testcase_finalize();
}
