// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// test_soc_periph_i2c_interrupts
// For each I2C instance, trigger the following IRQs
//  - IC_START_DET
//  - IC_STOP_DET
//  - IC_ACTIVITY
//  - IC_TX_ABRT
//  - IC_TX_EMPTY
//  - IC_TX_OVER
//  - IC_RX_FULL
//  - IC_RX_OVER
//  - IC_RX_UNDER

#include <critical_section.h>
#include <dw_i2c/drv_i2c.h>
#include <log.h>
#include <memorymap.h>
#include <platform.h>
#include <stdbool.h>
#include <testutils.h>
#include <timer.h>

// quite arbitrary, should change in the future
#define EXTERNAL_DEVICE_POWERUP_DELAY_US 1
#define I2C_SLAVE_ADDR 0x03c
#define I2C_SLAVE_WRITE_ADDR 0xc0
#define I2C_LPBK_ADDRESS 0x3a
#define I2C_MSG_SIZE_BYTES 4

struct dw_i2c i2c_peripheral;
int64_t key;
bool triggered = false;
uint32_t expected_interrupt;

// Common initial setup
int setup_test_isr(struct dw_i2c *i2c_periph, uint32_t interrupt) {
  int ret;

  // Disable interrupts in general
  key = arch_irq_lock();
  expected_interrupt = interrupt;

  // Clear all interrupts
  readl(&(i2c_periph->regs->ic_clr_intr));

  // Configure
  ret = designware_i2c_ops.configure(i2c_periph->regs, IC_ENABLE_0B, interrupt,
                                     IC_RX_TL, IC_TX_TL);
  if (!CHECK_TRUE(ret == TEST_SUCCESS, "*** Failed to configure!\n"))
    return TEST_FAILURE;

  // Enable interrupts in PLIC
  designware_i2c_ops.setup_interrupt(i2c_periph);

  return TEST_SUCCESS;
}

// Common check if the interrupt is triggered
int check_test_isr(uint32_t interrupt) {
  uint64_t base;
  // Enable interrupts in general
  arch_irq_unlock(key);

  /* Wait for the maximum of 2ms and minimum of 1ms before checking if
   * interrupts are generated, in the case another interrupt is generated before
   * the one of concern
   */
  udelay(1);
  base = get_timer(0);
  while (!triggered && (get_timer(base) < 10))
    ;

  return CHECK_TRUE(triggered, "*** Interrupt %u was not triggered!\n",
                    interrupt)
             ? TEST_SUCCESS
             : TEST_FAILURE;
}

int test_isr_start_det(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_START_DET test begins.\n");
  ret = setup_test_isr(i2c_periph, IC_START_DET);
  if (ret)
    return TEST_FAILURE;

  // Send a message, which should produce a start condition
  writel('a' | IC_STOP, &(i2c_periph->regs->ic_cmd_data));

  return check_test_isr(IC_START_DET);
}

int test_isr_stop_det(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_STOP_DET test begins.\n");
  ret = setup_test_isr(i2c_periph, IC_STOP_DET);
  if (ret)
    return TEST_FAILURE;

  // Send a message, with a stop condition
  writel('a' | IC_STOP, &(i2c_periph->regs->ic_cmd_data));

  return check_test_isr(IC_STOP_DET);
}

int test_isr_activity(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_ACTIVITY test begins.\n");
  ret = setup_test_isr(i2c_periph, IC_ACTIVITY);
  if (ret)
    return TEST_FAILURE;

  // Send a message, which should produce activity
  writel('a' | IC_STOP, &(i2c_periph->regs->ic_cmd_data));

  return check_test_isr(IC_ACTIVITY);
}

int test_isr_tx_abrt(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_TX_ABRT test begins.\n");
  ret = setup_test_isr(i2c_periph, IC_TX_ABRT);
  if (ret)
    return TEST_FAILURE;

  // Try to produce an abort
  writel('a' | IC_STOP, &(i2c_periph->regs->ic_cmd_data));

  return check_test_isr(IC_TX_ABRT);
}

int test_isr_tx_empty(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_TX_EMPTY test begins.\n");
  ret = setup_test_isr(i2c_periph, IC_TX_EMPTY);
  if (ret)
    return TEST_FAILURE;

  // TX buffer is already empty

  return check_test_isr(IC_TX_EMPTY);
}

int test_isr_tx_over(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_TX_OVER test begins.\n");

  // Setting different TAR and SAR, to disable loop-back. Otherwise the
  // transmitt would be too fast
  ret = setup_test_isr(i2c_periph, IC_TX_OVER);
  if (ret)
    return TEST_FAILURE;

  int i = 0;
  // Issue commands while the TX buffer is not full
  while (readl(&i2c_periph->regs->ic_status) & IC_STATUS_TFNF) {
    writel(i | IC_STOP, &(i2c_periph->regs->ic_cmd_data));
    i++;
  }
  // Once TX buffer is full, issue one more command to trigger the overflow
  writel(i | IC_STOP, &(i2c_periph->regs->ic_cmd_data));

  return check_test_isr(IC_TX_OVER);
}

int test_isr_rx_full(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_RX_FULL test begins.\n");

  // Set same TAR as SAR
  ret = setup_test_isr(i2c_periph, IC_RX_FULL);
  if (ret)
    return TEST_FAILURE;

  // Try to fill RX buffer
  uint8_t buffer[256]; // Reserving for maximum possible depth
  struct i2c_msg write_msg;
  write_msg.addr = I2C_LPBK_ADDRESS;
  write_msg.buf = buffer;
  write_msg.flags = 0; // Write
  write_msg.len = (uint32_t)i2c_periph->regs->ic_rx_tl + 1;

  // Consecutive writes need more care and thus xfer is used
  designware_i2c_ops.xfer(i2c_periph, &write_msg, 1);
  if (ret)
    return TEST_FAILURE;

  return check_test_isr(IC_RX_FULL);
}

int test_isr_rx_over(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_RX_OVER test begins.\n");

  // Set same TAR as SAR
  ret = setup_test_isr(i2c_periph, IC_RX_OVER);
  if (ret)
    return TEST_FAILURE;

  // Overflow the RX buffer
  int32_t rx_buffer_depth = ((i2c_periph->regs->comp_param1 >> 8) & 0xFF) + 1;
  LOG_DBG("(test_isr_rx_over) RX buffer is of depth %u.\n", rx_buffer_depth);

  uint8_t buffer[256]; // Reserving for maximum possible depth
  struct i2c_msg write_msg;
  write_msg.addr = I2C_LPBK_ADDRESS;
  write_msg.buf = buffer;
  write_msg.flags = 0; // Write
  write_msg.len = rx_buffer_depth + 1;

  // Consecutive writes need more care and thus xfer is used
  ret = designware_i2c_ops.xfer(i2c_periph, &write_msg, 1);
  if (ret)
    return TEST_FAILURE;

  return check_test_isr(IC_RX_OVER);
}

int test_isr_rx_under(struct dw_i2c *i2c_periph) {
  int ret;

  LOG_INF("*** IC_RX_UNDER test begins.\n");
  ret = setup_test_isr(i2c_periph, IC_RX_UNDER);
  if (ret)
    return TEST_FAILURE;

  // Trigger the interrupt by reading the empty buffer
  readl(&(i2c_periph->regs->ic_cmd_data));
  readl(&(i2c_periph->regs->ic_cmd_data));

  check_test_isr(IC_RX_UNDER);
  return ret;
}

void test_soc_periph_i2c_interrupts(void *i2c_base_address) {
  int ret;

  // Initialize the device
  printf("Probing the device.\n");
  ret = designware_i2c_ops.probe(&i2c_peripheral, i2c_base_address);
  if (!CHECK_TRUE(ret == TEST_SUCCESS, "*** Failed to probe!\n"))
    return;

  designware_i2c_ops.set_address(i2c_peripheral.regs, I2C_SLAVE_ADDR);
  designware_i2c_ops.set_slave_address(i2c_peripheral.regs, I2C_LPBK_ADDRESS);

  ret = designware_i2c_ops.set_bus_speed(&i2c_peripheral, I2C_SPEED_FAST_RATE);
  if (!CHECK_TRUE(ret == TEST_SUCCESS, "*** Failed to set bus speed!\n"))
    return;

  CHECK_TRUE(test_isr_start_det(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_stop_det(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_activity(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_tx_abrt(&i2c_peripheral) == TEST_SUCCESS);

  // Enable loopback to prevent TX_ABRT event that stalls the TX_FIFO
  // Enable loopback by setting SAR==TAR
  designware_i2c_ops.set_address(i2c_peripheral.regs, I2C_LPBK_ADDRESS);

  CHECK_TRUE(test_isr_tx_empty(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_tx_over(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_rx_full(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_rx_over(&i2c_peripheral) == TEST_SUCCESS);
  CHECK_TRUE(test_isr_rx_under(&i2c_peripheral) == TEST_SUCCESS);
}

void verify_interrupt(unsigned int irq_source) {
  uint32_t int_sts = 0;

  // Makes sure that the IRQ comes from the I2C instance we are currently
  // testing
  if (!(((irq_source == IRQ_SOC_PERIPH_I2C_0_SOURCE) &&
         ((uintptr_t)i2c_peripheral.regs == SOC_PERIPH_I2C_0_BASE)) ||
        ((irq_source == IRQ_SOC_PERIPH_I2C_1_SOURCE) &&
         ((uintptr_t)i2c_peripheral.regs == SOC_PERIPH_I2C_1_BASE)))) {
    return;
  }

  int_sts = get_int_status(&i2c_peripheral);

  if (int_sts & expected_interrupt) {
    triggered = true;
  }

  if (int_sts & IC_START_DET) {
    readl(&(i2c_peripheral.regs->ic_clr_start_det));
  }
  if (int_sts & IC_STOP_DET) {
    readl(&(i2c_peripheral.regs->ic_clr_stop_det));
  }
  if (int_sts & IC_ACTIVITY) {
    writel(readl(&(i2c_peripheral.regs->ic_intr_mask)) & ~IC_ACTIVITY,
           &(i2c_peripheral.regs->ic_intr_mask));
  }
  if (int_sts & IC_TX_EMPTY) {
    writel(readl(&(i2c_peripheral.regs->ic_intr_mask)) & ~IC_TX_EMPTY,
           &(i2c_peripheral.regs->ic_intr_mask));
  }
  if (int_sts & IC_RX_FULL) {
    writel(readl(&(i2c_peripheral.regs->ic_intr_mask)) & ~IC_RX_FULL,
           &(i2c_peripheral.regs->ic_intr_mask));
  }

  if (int_sts & IC_TX_ABRT) {
    // Get Tx fifo out of its flushed/reset state
    // See note in section 2.8.1.2 of dw_apb_i2c 2.03a spec
    readl(&(i2c_peripheral.regs->ic_clr_tx_abrt));
  }
}

int main() {
  testcase_init();
  test_soc_periph_i2c_interrupts((void*)SOC_PERIPH_I2C_0_BASE);
  test_soc_periph_i2c_interrupts((void*)SOC_PERIPH_I2C_1_BASE);

  return testcase_finalize();
}
