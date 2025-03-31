// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***


#include <testutils.h>
#include <platform.h>
#include <stdbool.h>
#include <critical_section.h>

#include <dw_gpio/drv_gpio.h>

static volatile bool gpio_triggered = false;
static volatile bool gpio_triggered_pin_irq = false;

void verify_interrupt(unsigned int irq_source) {
  if (irq_source == IRQ_SOC_PERIPH_GPIO_SOURCE) {
    gpio_triggered = true;
  }
}

void gpio_irq_handler_pin_loopback_out()
{
  gpio_triggered_pin_irq = true;
}

void test_gpio_irq(uint32_t test_pin_1, uint32_t test_pin_2) {
  int ret;

  gpioSetDirection(test_pin_1, kGpioOutputDirection);
  gpioSetDirection(test_pin_2, kGpioInputDirection);
  gpioSetOutput(test_pin_1, kGpioOutputLow);

  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();

  // Enable GPIO interrupt
  gpioSetupInterrupt();
  registerGpioCallback(test_pin_2, gpio_irq_handler_pin_loopback_out);

  arch_irq_unlock(key);

  ret = gpioReadInput(test_pin_2);
  CHECK_TRUE(ret == kGpioOutputLow);

  /* Verify that no interrupts have been triggered yet */
  CHECK_TRUE(!gpio_triggered);
  CHECK_TRUE(!gpio_triggered_pin_irq);

  /* Interrupt should trigger only here*/
  gpioSetOutput(test_pin_1, kGpioOutputHigh);
  ret = gpioReadInput(test_pin_2);
  CHECK_TRUE(ret == kGpioOutputHigh);

  CHECK_TRUE(gpio_triggered);
  CHECK_TRUE(gpio_triggered_pin_irq);
}


void test_gpio(uint32_t test_pin_1, uint32_t test_pin_2) {
  int ret;

  // gpio pin 0 is hardwired to pin 1 on the testbench
  gpioSetDirection(test_pin_1, kGpioOutputDirection);
  gpioSetDirection(test_pin_2, kGpioInputDirection);

  gpioSetOutput(test_pin_1, kGpioOutputLow);
  ret = gpioReadInput(test_pin_2);
  CHECK_TRUE(ret == kGpioOutputLow, "GPIO_1=%d, GPIO_2=%d", test_pin_1, test_pin_2);

  gpioSetOutput(test_pin_1, kGpioOutputHigh);
  ret = gpioReadInput(test_pin_2);
  CHECK_TRUE(ret == kGpioOutputHigh, "GPIO_1=%d, GPIO_2=%d", test_pin_1, test_pin_2);

  gpioSetDirection(test_pin_1, kGpioInputDirection);
  gpioSetDirection(test_pin_2, kGpioOutputDirection);

  gpioSetOutput(test_pin_2, kGpioOutputLow);
  ret = gpioReadInput(test_pin_1);
  CHECK_TRUE(ret == kGpioOutputLow, "GPIO_1=%d, GPIO_2=%d", test_pin_1, test_pin_2);

  gpioSetOutput(test_pin_2, kGpioOutputHigh);
  ret = gpioReadInput(test_pin_1);
  CHECK_TRUE(ret == kGpioOutputHigh, "GPIO_1=%d, GPIO_2=%d", test_pin_1, test_pin_2);
}

int main() {
  testcase_init();

  // Set all GPIOs as output to avoid reading Xs
  for (uint32_t pin = 0; pin < DW_GPIO_PWIDTH_A; pin++)
  {
    gpioSetDirection(pin, kGpioOutputDirection);
  }
  // Test gpio loopback
  test_gpio(GPIO_PIN_LOOPBACK_OUT, GPIO_PIN_LOOPBACK_IN);
#ifndef NO_INTERRUPTS
  test_gpio_irq(GPIO_PIN_LOOPBACK_OUT, GPIO_PIN_LOOPBACK_IN);
#endif // NO_INTERRUPTS

  return testcase_finalize();
}
