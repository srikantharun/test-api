#include <kse/kse_utils.h>
#include <stdint.h>
#include <testutils.h>

int main() {
  uint16_t sub_token = 0;
  uint32_t allow_error=0;
  testcase_init();

  kse_execute_after_reset_sequence();

  LOG_INF("Start test for command InitRot");

  kse_clear_irq();
  kse_execute_cmd(KSE3_CMD_INIT_ROT, sub_token, allow_error);
  kse_print_ids();

  return testcase_finalize();
}
