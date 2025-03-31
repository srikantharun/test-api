// EMMC tests
//
// test_emmc_dma_xfer
// - Init EMMC controller
// - Configure EMMC card
// - Set both of them to standard mode, 8-bit transfer width
// - Perform a DMA transfer to the EMMC
// - Perform another DMA transfer to transfer back the data to the AXI slave
// - Compare TX and RX buffers within the AXI slave and make sure they match

#include <cdns_emmc/drv_emmc.h>
#include <cdns_emmc/emmc_card_regs.h>
#include <printf.h>
#include <rng.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <timer.h>
#include <util.h>
#include <uvm_ipc/uvm_sw_ipc.h>

#define BUFFER_SIZE (EMMC_MAX_BLOCK_SIZE / 8)

uint64_t __attribute__((
    aligned(64), section(".sys_spm.src_buf"))) src_buf[BUFFER_SIZE] = {0};
uint64_t __attribute__((
    aligned(64), section(".sys_spm.dst_buf"))) dst_buf[BUFFER_SIZE] = {0};

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

#ifdef PLATFORM_QEMU
void test_qemu_minimal() {
  // Minimal QEMU-specific test
  printf("QEMU: Resetting the core...\n");
  reset_core();

  printf("QEMU: Writing to PHY register 0x01...\n");
  write_phy_reg(0x01, 0xAABBCCDD);
  uint32_t phy_val = read_phy_reg(0x01);
  ASSERT(phy_val == 0xAABBCCDD);

  printf("QEMU: PHY register test passed!\n");
}
#endif

void test_emmc_dma_xfer() {
  uint32_t emmc_buf_addr = 0x0u;
  uintptr_t src_buf_addr = (uintptr_t)src_buf;
  uintptr_t dst_buf_addr = (uintptr_t)dst_buf;
  uint64_t seed = 0xcafedecadeadbeef;

  printf("\r\n===== emmc dma transfer test ======\r\n");
  printf("SDR, 1b, 25 MHz\r\n");

  // --------------------------------------------------------------------------
  printf("************************************************\r\n");
#ifndef PLATFORM_QEMU
  emmc_card_display_state();
  emmc_select_card();
  emmc_card_display_state();

  emmc_set_standard_mode(8); // SDR, 8-bit
  udelay(10);
  emmc_card_display_state();

  printf("************************************************\n");
  printf("Initializing source buffer...\n");
#endif // !PLATFORM_QEMU
  for (int i = 0; i < BUFFER_SIZE; i++) {
    src_buf[i] = xorshift64(&seed);
  }

  printf("Source buffer initialized...\n");

  printf("Write data...\n");
  ASSERT(emmc_dma_write_xfer(src_buf_addr, emmc_buf_addr, 1) == 0);
  printf("Transfer complete!\n");

  printf("Read data...\r\n");
  ASSERT(emmc_dma_read_xfer(emmc_buf_addr, dst_buf_addr, 1) == 0);

  // Compare
  printf("Compare buffers\r\n");
  CHECK_EQUAL_INT(0, memcmp((void *)src_buf_addr, (void *)dst_buf_addr,
                            EMMC_MAX_BLOCK_SIZE));
}

int main() {
  testcase_init();

#ifdef PLATFORM_QEMU
  test_qemu_minimal();
#else
  uint16_t sd_card_rca = 0x1234u;

  emmc_disable_reset();
  emmc_set_clock_stable(true);
  emmc_sd_host_init();
  printf("SD host initialized!\n");
  emmc_card_init(true, sd_card_rca);
#endif // PLATFORM_QEMU

  test_emmc_dma_xfer();
  return testcase_finalize();
}
