// EMMC tests
//
// test_emmc_preload: Test that EMMC softmodel can be successfully preloaded
// - Preload the EMMC user partition with data. Each data is expected to correspond to its address
// - Init EMMC controller
// - Configure EMMC card - Set both of them to standard mode, 8-bit transfer width
// - Perform a DMA transfer from the EMMC
// - Verify the data received

#include <cdns_emmc/drv_emmc.h>
#include <cdns_emmc/emmc_card_regs.h>
#include <printf.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <timer.h>
#include <util.h>

#define BUFFER_SIZE (EMMC_MAX_BLOCK_SIZE / 8)

uint64_t __attribute__((aligned(64), section(".sys_spm.dst_buf"))) dst_buf[BUFFER_SIZE] = {0};

const char *STATE_NAMES[] = {"Idle", "Ready", "Ident", "Stby", "Tran", "Data",
                             "Rcv",  "Prg",   "Dis",   "Btst", "Slp"};

void emmc_card_display_state() {
  uint32_t card_status = emmc_card_get_status();
  uint32_t state = (card_status >> 9) & 0x0f;
  const char *state_name = "Reserved";

  CHECK_EQUAL_INT((card_status & STATUS_ERRORS), 0, "Status errors detected!");

  if (state < ARRAY_LENGTH(STATE_NAMES)) {
    state_name = STATE_NAMES[state];
  }

  printf("SD card state: %s\r\n", state_name);
}

void test_emmc_preload() {
  uintptr_t dst_buf_addr = (uintptr_t)dst_buf;
  uint32_t emmc_buf_addr = 0x0u;
  uint16_t sd_card_rca = 0x1234u;

  // --------------------------------------------------------------------------
  emmc_disable_reset();
  emmc_set_clock_stable(true);
  emmc_sd_host_init();
  printf("SD host initialized!\n");
  emmc_card_init(true, sd_card_rca);

  emmc_card_display_state();
  emmc_select_card();
  emmc_card_display_state();

  emmc_set_standard_mode(8); // SDR, 8-bit
  udelay(10);
  emmc_card_display_state();

  // EMMC memory is backdoor-loaded from the UVM
  printf("Read data...\r\n");
  ASSERT(emmc_dma_read_xfer(emmc_buf_addr, dst_buf_addr, 1) == 0);

  // Compare
  printf("Check received data\r\n");
  for (int i = 0 ; i<EMMC_MAX_BLOCK_SIZE; i++) {
    if (!CHECK_EQUAL_HEX(*(uint8_t*)(dst_buf_addr + i), (uint8_t)i)) {
      break;
    }
  }
}

int main() {
  testcase_init();
  // FIXME: Check interrupt status
  // https://git.axelera.ai/prod/europa/-/issues/1493
  test_emmc_preload();
  return testcase_finalize();
}
