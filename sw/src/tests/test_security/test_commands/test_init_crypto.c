#include <kse/kse_utils.h>
#include <stdint.h>
#include <testutils.h>

int main() {
  uint16_t sub_token = 0;

  testcase_init();

  kse_execute_after_reset_sequence();

  LOG_INF("Start test for command InitCrypto");

  //send InitCrypto command with the information that error shall happen
  uint32_t allow_error=1;
  LOG_INF("Sending InitCrypto without InitRot with allow error=%0d", allow_error);
  kse_execute_cmd(KSE3_CMD_INIT_CRYPTO, sub_token, allow_error);

  allow_error=0;
  LOG_INF("Sending InitCrypto after InitRot with allow error=%0d", allow_error);
  //send InitRot command
  kse_execute_cmd(KSE3_CMD_INIT_ROT, sub_token, allow_error);
  //send InitCrypto command with the information that error shall not happen
  //prepare data for Init Crypto
  prepare_data_for_cmd_init_crypto();
  //send InitCrypto command
  kse_execute_cmd(KSE3_CMD_INIT_CRYPTO, sub_token, allow_error);

  return testcase_finalize();
}
