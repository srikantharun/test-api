// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// test_soc_periph_i2c_slave_sm
// For both I2C IPs:
//  - Configure I2C in slave mode
//  - Initiate a write transfer from master I2C
//  - Compare RX and TX data
//  - Initiate a read transfer from master I2C
//  - Check that RD_REQ IRQ triggers on each read transfer
//  - Compare RX and TX data
//  - Initiate a general write transfer from master I2C
//  - Check that GEN_CALL IRQ triggers
//

#include <clk/drv_clk.h>
#include <critical_section.h>
#include <dw_i2c/drv_i2c.h>
#include <log.h>
#include <memorymap.h>
#include <platform.h>
#include <std/std_basetype.h>
#include <std/std_bit.h>
#include <testutils.h>
#include <timer.h>
#include <uvm_ipc/uvm_sw_ipc.h>

// Arbitrary: see hw/impl/europa/blocks/soc_periph/dv/spike_tb/cpp/dpi_devices.h
#define I2C0_MASTER_BASE 0xC0000000 // Fake address to access I2C0 master
#define I2C1_MASTER_BASE 0xC1000000 // Fake address to access I2C0 master

#define I2C_SLAVE_ADDR 0x3a // Arbitrary
#define I2C_READ_ADDR 0x44  // Arbitrary

#define BUF_LEN 4 // Transfer size in bytes

// See section 3.2.1 of i2c master doc
// Input clock is 48Mhz
#define I2C_MASTER_INPUT_CLK MHz(48)
#define I2C_MASTER_SM_PRESCALE                                                 \
  ((I2C_MASTER_INPUT_CLK / (5 * I2C_SPEED_STANDARD_RATE)) - 1)

#define CTR_EN ((uint8_t)1 << 7)

#define CR_STA ((uint8_t)1 << 7)
#define CR_STO ((uint8_t)1 << 6)
#define CR_RD ((uint8_t)1 << 5)
#define CR_WR ((uint8_t)1 << 4)
#define CR_ACK ((uint8_t)1 << 3)

#define SR_TIP ((uint8_t)1 << 1)

// Registers inside
typedef struct {
  reg8_t prer_lo;
  reg8_t prer_hi;
  reg8_t ctr;
  reg8_t txr_rxr;
  reg8_t cr_sr;
} opencore_i2c_master;

_Static_assert(
    offsetof(opencore_i2c_master, cr_sr) == 0x4,
    "opencore_i2c_master: last register has not the correct address offset");

// Global slave and master handles
// This avoids passing them around in every function
static struct dw_i2c i2c_slave;
static opencore_i2c_master *i2c_master;

void configure_i2c_master() {
  i2c_master->prer_lo = (uint8_t)I2C_MASTER_SM_PRESCALE;
  i2c_master->prer_hi = (uint8_t)(I2C_MASTER_SM_PRESCALE >> 8u);
  // Enable core
  i2c_master->ctr |= CTR_EN;
}

void wait_for_xfer_done() {
  while (i2c_master->cr_sr & SR_TIP)
    ;
}

void i2c_master_write_xfer(struct i2c_msg *msg) {
  // First we send the slave address + write command
  i2c_master->txr_rxr = ((uint8_t)msg->addr << 1);
  i2c_master->cr_sr = CR_WR | CR_STA;
  wait_for_xfer_done();

  // Then we send the data
  for (uint64_t i = 0; i < msg->len; i++) {
    uint8_t cmd = CR_WR;
    i2c_master->txr_rxr = msg->buf[i];
    if (i == (msg->len - 1)) {
      cmd |= CR_STO;
    }
    i2c_master->cr_sr = cmd;
    wait_for_xfer_done();
  }
}

bool wait_for_interrupt(char *int_path) {
  int wait_time_us = 10;
  int cycle = 0;
  bool triggered = false;
  while ((cycle < wait_time_us) && !triggered) {
    udelay(1);
    triggered = (uvm_sw_ipc_hdl_read(int_path) == 1);
    cycle++;
  }

  return triggered;
}

int i2c_slave_handle_read(char *int_path, uint8_t resp_data) {
  bool triggered = wait_for_interrupt(int_path);

  if (triggered) {
    // Send data to return to the master and clear interrupts
    writel(resp_data, &(i2c_slave.regs->ic_cmd_data));
    readl(&(i2c_slave.regs->ic_clr_rd_req));
    // Make sure the interrupt is inactive
    CHECK_EQUAL_HEX(uvm_sw_ipc_hdl_read(int_path), 0);
    return TEST_SUCCESS;
  } else {
    return TEST_FAILURE;
  }
}

void i2c_master_read_xfer(struct i2c_msg *msg, uint8_t *resp_buf,
                          char *int_path) {
  // First we send the slave address + read command
  i2c_master->txr_rxr = ((uint8_t)msg->addr << 1) | (uint8_t)1;
  i2c_master->cr_sr = CR_WR | CR_STA;
  wait_for_xfer_done();

  // Then we ask for data
  for (uint64_t i = 0; i < msg->len; i++) {
    uint8_t cmd = CR_RD;
    if (i == (msg->len - 1)) {
      cmd |= CR_STO | CR_ACK; // Send  stop + nack to end transfer
    }
    i2c_master->cr_sr = cmd;
    // Handle the read request on the slave side
    ASSERT(i2c_slave_handle_read(int_path, resp_buf[i]) == TEST_SUCCESS);
    wait_for_xfer_done();
    msg->buf[i] = i2c_master->txr_rxr;
  }
}

void test_soc_periph_i2c_slave_sm(void *i2c_base_address,
                                  void *i2c_master_base_address,
                                  char *int_path) {
  i2c_master = i2c_master_base_address;
  ASSERT(designware_i2c_ops.probe(&i2c_slave, i2c_base_address) == 0);
  designware_i2c_ops.set_slave_address(i2c_slave.regs, I2C_SLAVE_ADDR);
  configure_i2c_master();
  ASSERT(set_slave_mode(&i2c_slave, I2C_SLAVE_ADDR) == 0);
  // Set RX and TX fifo levels to 1
  ASSERT(designware_i2c_ops.configure(i2c_slave.regs, 0, 0, 0, 0) == 0);

  //--------------------------------------------------
  // Write transfer
  //--------------------------------------------------
  uint8_t tx_buf[BUF_LEN] = {0xca, 0xfe, 0xde, 0xca};
  uint32_t raw_int_stat;
  struct i2c_msg write_msg = {
      .flags = 0, .len = 4, .buf = tx_buf, .addr = I2C_SLAVE_ADDR};
  i2c_master_write_xfer(&write_msg);
  for (int i = 0; i < BUF_LEN; i++) {
    raw_int_stat = readl(&i2c_slave.regs->ic_raw_intr_stat);
    // Check that RX FIFO is not empty
    ASSERT((raw_int_stat & IC_RX_FULL) > 0);
    uint8_t rx_byte = readl(&i2c_slave.regs->ic_cmd_data);
    printf("Received data from master: %x\r\n", rx_byte);
    CHECK_EQUAL_HEX(tx_buf[i], rx_byte);
  }
  // Check that RX FIFO is empty
  raw_int_stat = readl(&i2c_slave.regs->ic_raw_intr_stat);
  ASSERT((raw_int_stat & IC_RX_FULL) == 0);

  //--------------------------------------------------
  // Read transfer
  //--------------------------------------------------
  uint8_t rx_buf[BUF_LEN] = {0};
  struct i2c_msg read_msg = {
      .flags = 0, .len = 4, .buf = rx_buf, .addr = I2C_SLAVE_ADDR};

  // Enable RD_REQ interrupt
  readl(&(i2c_slave.regs->ic_clr_intr)); // Clear interrupts
  ASSERT(
      designware_i2c_ops.configure(i2c_slave.regs, 0, IC_RD_REQ, 0, 0) == 0);

  i2c_master_read_xfer(&read_msg, tx_buf, int_path);
  for (int i = 0; i < BUF_LEN; i++) {
    printf("Received data from slave: %x\r\n", rx_buf[i]);
    CHECK_EQUAL_HEX(tx_buf[i], rx_buf[i]);
  }

  //--------------------------------------------------
  // General call
  //--------------------------------------------------
  // Enable GEN_CALL interrupt
  readl(&(i2c_slave.regs->ic_clr_intr)); // Clear interrupts
  ASSERT(
      designware_i2c_ops.configure(i2c_slave.regs, 0, IC_GEN_CALL, 0, 0) == 0);
  write_msg.len = 0;
  write_msg.addr = 0x0; // Just broadcast an empty message
  CHECK_EQUAL_HEX(uvm_sw_ipc_hdl_read(int_path), 0);
  i2c_master_write_xfer(&write_msg);
  ASSERT(wait_for_interrupt(int_path));
}

int main() {
  testcase_init();
  printf("Configuring I2C0 master!\r\n");
  printf("Testing I2C0\r\n");
  test_soc_periph_i2c_slave_sm((void *)SOC_PERIPH_I2C_0_BASE,
                               (void *)I2C0_MASTER_BASE,
                               "spike_top_tb.th.u_soc_periph_p.o_i2c_0_int");
  printf("Testing I2C1\r\n");
  test_soc_periph_i2c_slave_sm((void *)SOC_PERIPH_I2C_1_BASE,
                               (void *)I2C1_MASTER_BASE,
                               "spike_top_tb.th.u_soc_periph_p.o_i2c_1_int");
  return testcase_finalize();
}
