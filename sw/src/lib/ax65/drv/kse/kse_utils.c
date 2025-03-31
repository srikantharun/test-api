#include "kse/kse_utils.h"
#include <regutils.h>
#include <printf.h>
#include <testutils.h>

/* Implement the after reset sequence */
uint32_t kse_execute_after_reset_sequence()
{
    uint32_t ctrl;
    uint8_t status;

    //wait until CMD_CTRL has 0 on bit index 0 (indicating that is not busy)
    do {
      ctrl = get_reg_u32(ADDR_CMD_CTRL);
    } while (ctrl & 1);

    //clear interrupt
    set_reg_u32(ADDR_INT_CTRL, 0x0);

    //check status
    status =  get_reg_u32(ADDR_CMD_STATUS) & 0xFF;
    if (!(CHECK_TRUE((status==KSE3_SUCCESS), "Unexpected comand status"))) {
      LOG_ERR("unexpected comand status 0x%02x", status);
      return 0;
    }

    // check tracker
    uint32_t trk;
    trk = get_reg_u32(ADDR_CMD_TRK);
    if (!(CHECK_TRUE((trk==0xFFFFFF00), "Unexpected comand tracker"))) {
      LOG_ERR("unexpected comand tracker=0x%02x and ctrl=0x%02x", trk, ctrl);
      return 0;
    }

    return 1;
}

/* Process a command, including polling and status retrival */
uint32_t kse_execute_cmd( uint8_t token, uint16_t sub_token, uint32_t allow_error)
{
    uint32_t ctrl;
    uint8_t status;

    //start the command
    set_reg_u32(ADDR_CMD_CTRL, (uint32_t)token << 24 | sub_token << 16 | 1);

    //wait command done
    do {
      ctrl = get_reg_u32(ADDR_CMD_CTRL);
    } while (ctrl & 1);

    //clear interrupt
    set_reg_u32(ADDR_INT_CTRL, 0x0);

    //check status
    status =  get_reg_u32(ADDR_CMD_STATUS) & 0xFF;
    if(allow_error) {
      if (!(CHECK_TRUE((status!=KSE3_SUCCESS), "Unexpected command status"))) {
        LOG_ERR("Expected test to fail but test passed. Status equal to 0x%02x", status);
        return 0;
      }
    }
    else {
      if (!(CHECK_TRUE((status==KSE3_SUCCESS), "Unexpected comand status"))) {
        LOG_ERR("unexpected comand status 0x%02x", status);
        return 0;
      }
      // check tracker
      uint32_t trk;
      trk = get_reg_u32(ADDR_CMD_TRK);
      if (!(CHECK_TRUE((trk==((~(ctrl)) | 0x000000FF)), "Unexpected comand tracker"))) {
        LOG_ERR("unexpected comand tracker=0x%02x and ctrl=0x%02x", trk, ctrl);
        return 0;
      }
    }

    return 1;
}

/* Clear interrupt */
void kse_clear_irq()
{
  //clear interrupt that is generated at reset
  set_reg_u32(ADDR_INT_CTRL, 0x0);
}

/* Print HW and FW Revision */
void kse_print_ids()
{
  /* Display some informations regarding the testbench */
  LOG_INF("");
  LOG_INF("KSE3 Details:");
  LOG_INF("- HW_ID:    0x%08x", get_reg_u32(ADDR_HW_ID));
  LOG_INF("- NAGRA_ID: 0x%08x", get_reg_u32(ADDR_NAGRA_ID));
  LOG_INF("");
}

/* Prepare data for InitCrypto command */
void prepare_data_for_cmd_init_crypto()
{
  // 1. Write Length of personalization string to KSE3 DRAM
  uint32_t perso_string_length = 64;
  LOG_INF("Writting perso string length");
  set_reg_u32(KSE3_DRAM_OFFSET_PERSO_STR_LEN, perso_string_length);
  // 2. Copy TRNG configuration to KSE3 DRAM (send the default value {0xC0, 0x9C, 0x00, 0x02, 0x00, 0x00, 0x2A, 0x00})
  LOG_INF("Writting TRNG configuration");
  set_reg_u32(KSE3_DRAM_OFFSET_TRNG_CFG,    0x02009CC0);
  set_reg_u32(KSE3_DRAM_OFFSET_TRNG_CFG+4,  0x002A0000);
  // 3. Copy Personalization string to KSE3 DRAM
  uint32_t addr;
  uint32_t i;
  LOG_INF("Writting person string length");
  for (i=0; i<perso_string_length; i=i+4) {
    addr = KSE3_DRAM_OFFSET_PERSO_STR_VAL + i;
    set_reg_u32 (addr, 0xDEADBEEF);
  }
}
