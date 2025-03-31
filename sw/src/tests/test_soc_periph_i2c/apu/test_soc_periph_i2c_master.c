// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// test_soc_periph_i2c_master_sm
// For both I2C IPs
// 1. Configure I2C to operate as master in standard mode
// 2. Write 4 bytes into the slave memory
// 3. Read back these 4 bytes
// 4. Compare sent and received payloads and verify they match

#include <critical_section.h>
#include <dw_i2c/drv_i2c.h>
#include <log.h>
#include <memorymap.h>
#include <platform.h>
#include <testutils.h>
#include <timer.h>

// quite arbitrary, should change in the future
#define EXTERNAL_DEVICE_POWERUP_DELAY_US 1
#define IC_DEFAULT_SLAVE_ADDR 0x03c
#define I2C_SLAVE_WRITE_ADDR 0xc0
#define I2C_MSG_SIZE_BYTES 4

struct dw_i2c i2c_peripheral;

void test_soc_periph_i2c_master_sm(void *i2c_base_address) {
  struct i2c_regs *i2c_registers = i2c_base_address;
  struct dw_i2c i2c_peripheral;
  i2c_peripheral.regs = i2c_registers;
  int ret;
  // First byte of a message is the address we're writing to/reading from
  uint8_t write_buf[I2C_MSG_SIZE_BYTES + 1] = {I2C_SLAVE_WRITE_ADDR, 0xca, 0xfe,
                                               0xde, 0xca};
  uint8_t read_buf[I2C_MSG_SIZE_BYTES] = {0};
  struct i2c_msg write_message = {.addr = 0x3c,
                                  .buf = write_buf,
                                  .len = I2C_MSG_SIZE_BYTES + 1,
                                  .flags = 0};
  struct i2c_msg read_message = {.addr = 0x3c,
                                 .buf = read_buf,
                                 .len = I2C_MSG_SIZE_BYTES,
                                 .flags = I2C_M_RD};

  // Wait for memory device to powerup
  udelay(EXTERNAL_DEVICE_POWERUP_DELAY_US);

  printf("Starting transfer!\r\n");
  designware_i2c_ops.set_address(i2c_registers, IC_DEFAULT_SLAVE_ADDR);
  // Checks if the peripheral is valid and initializes it
  ret = designware_i2c_ops.probe(&i2c_peripheral, (void *)i2c_base_address);
  ASSERT(ret == TEST_SUCCESS);

  // Set bus speed
  ret = designware_i2c_ops.set_bus_speed(&i2c_peripheral,
                                         I2C_SPEED_STANDARD_RATE);
  ASSERT(ret == TEST_SUCCESS);

  // Send a write message to the slave
  printf("Sending write message!\r\n");
  ret = designware_i2c_ops.xfer(&i2c_peripheral, &write_message, 1);
  ASSERT(ret == TEST_SUCCESS);

  // First, send a write message to the slave to reset the address
  write_message.len = 1;
  ret = designware_i2c_ops.xfer(&i2c_peripheral, &write_message, 1);
  ASSERT(ret == TEST_SUCCESS);
  // Send a read message to the slave
  printf("Sending read message!\r\n");
  ret = designware_i2c_ops.xfer(&i2c_peripheral, &read_message, 1);
  ASSERT(ret == TEST_SUCCESS);

  printf("Comparing buffers!\r\n");
  CHECK_EQUAL_INT(memcmp(&write_buf[1], read_buf, I2C_MSG_SIZE_BYTES), 0);
}

int main() {
  testcase_init();
  printf("Testing I2C0\r\n");
  test_soc_periph_i2c_master_sm((void *)SOC_PERIPH_I2C_0_BASE);
  printf("Testing I2C1\r\n");
  test_soc_periph_i2c_master_sm((void *)SOC_PERIPH_I2C_1_BASE);
  return testcase_finalize();
}
