#include <printf.h>
#include <stdbool.h>
#include <stdint.h>
#include <memorymap.h>
#include <testutils.h>

#define load(addr) *(volatile uint32_t *)addr

int main() {
  uintptr_t i2c0_ver_addr = SOC_PERIPH_I2C_0_BASE + 0xF8;
  uintptr_t i2c1_ver_addr = SOC_PERIPH_I2C_1_BASE + 0xF8;
  uintptr_t uart_sts_addr = SOC_PERIPH_UART_BASE + 0x7C;
  uintptr_t gpio_ver_addr = SOC_PERIPH_GPIO_BASE + 0x6C;
  uintptr_t spi_ver_addr = SOC_PERIPH_SPI_BASE + 0x5C;
  uintptr_t tim_ver_addr = SOC_PERIPH_TIMER_BASE+ 0xAC;
  uintptr_t emmc_ver_addr = SOC_PERIPH_EMMC_BASE + 0x7C;

  testcase_init();

  CHECK_EQUAL_HEX(0x3230332a, load(i2c0_ver_addr));
  CHECK_EQUAL_HEX(0x3230332a, load(i2c1_ver_addr));
  CHECK_EQUAL_HEX(0x3430332a, load(spi_ver_addr));
  CHECK_EQUAL_HEX(0x3231332a, load(tim_ver_addr));
  CHECK_EQUAL_HEX(0x3231342a, load(gpio_ver_addr));
  CHECK_EQUAL_HEX(0x0, load(uart_sts_addr)); // UART should be inactive
  CHECK_EQUAL_HEX(0x6020002, load(emmc_ver_addr));

  return testcase_finalize();
}
