// GPIO tests
//
// test_soc_periph_gpio_output:
//
// 1. Set pins mode to output
// 2. Set their value to 0
// 3. For each pin:
//  3.1. Set it to 1
//  3.2. Verify its value from the UVM
//  3.3. Check that all the other pins are at 0
//
//
// test_soc_periph_gpio_input:
//
// 1. Set GPIO input to 0
// 2. Set pins mode to input
// 3. Enable interrupt in edge mode
// 4. For each pin:
//  4.1. Set its input to 1 in the tb
//  4.2. Wait for the interrupt
//  4.2. Check the pin value on the SOC_PERIPH's side
//  4.3. Check that all the other pins are at 0

#include <dw_gpio/drv_gpio.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <uvm_ipc/uvm_sw_ipc.h>

// Hacky solution: handler needs to be called explicitely
// since IRQ are not available on SOC_PERIPH SPIKE TB
void gpio_irq_handler(void);

static const char *gpio_oe_wires = "spike_top_tb.th.o_gpio_oe";

void test_soc_periph_gpio_output() {
  const char *gpio_wires = "spike_top_tb.th.o_gpio";

  // Set all pins to output
  for (int pin = 0; pin < DW_GPIO_PWIDTH_A; pin++) {
    gpioSetDirection(pin, kGpioOutputDirection);
    gpioSetOutput(pin, kGpioOutputLow);
  }

  // Check that all GPIOs are set to low and gpio_oe wires are set to 1
  CHECK_EQUAL_INT(0u, uvm_sw_ipc_hdl_read(gpio_wires));
  CHECK_EQUAL_INT(0xFFFFu, uvm_sw_ipc_hdl_read(gpio_oe_wires));

  // Set each pin to HIGH one-by-one
  for (int pin = 0; pin < DW_GPIO_PWIDTH_A; pin++) {
    gpioSetOutput(pin, kGpioOutputHigh);
    CHECK_EQUAL_INT(((uint64_t)1u << pin), uvm_sw_ipc_hdl_read(gpio_wires));
    gpioSetOutput(pin, kGpioOutputLow);
  }
}

void check_single_pin_active(int pin) {
  for (int i = 0; i < DW_GPIO_PWIDTH_A; i++) {
    int expected_val = (i == pin) ? 1 : 0;
    CHECK_EQUAL_INT(expected_val, gpioReadInput(i));
  }
}

void test_soc_periph_gpio_input() {
  const char *gpio_wire = "spike_top_tb.th.i_gpio";
  const char *gpio_wire_int = "spike_top_tb.th.o_gpio_int";

  uvm_sw_ipc_hdl_force(gpio_wire, 0u);

  for (int pin = 0; pin < DW_GPIO_PWIDTH_A; pin++) {
    gpioSetDirection(pin, kGpioInputDirection);
    CHECK_EQUAL_INT(0u, gpioReadInput(pin));
  }

  // Check that GPIO OE wires are set to LOW
  CHECK_EQUAL_INT(0u, uvm_sw_ipc_hdl_read(gpio_oe_wires));

  // Enable GPIO interrupt in edge mode
  gpioSetupInterrupt();

  for (int pin = 0; pin < DW_GPIO_PWIDTH_A; pin++) {
    uint64_t gpio_int;
    // Check that no interrupt is active
    CHECK_EQUAL_INT(0u, uvm_sw_ipc_hdl_read(gpio_wire_int));

    // Trigger interrupt
    uvm_sw_ipc_hdl_force(gpio_wire, ((uint64_t)1u << pin));
    do {
      gpio_int = uvm_sw_ipc_hdl_read(gpio_wire_int);
    } while (gpio_int == 0u);

    // Clear interrupt and check pin value
    gpio_irq_handler();
    check_single_pin_active(pin);

    uvm_sw_ipc_hdl_force(gpio_wire, 0u);
  }
}

int main() {
  testcase_init();
  test_soc_periph_gpio_output();
  test_soc_periph_gpio_input();
  return testcase_finalize();
}
