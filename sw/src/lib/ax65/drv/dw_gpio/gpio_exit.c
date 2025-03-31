#include <stdint.h>
#include <stddef.h>
#include <dw_gpio/drv_gpio.h>

void __attribute__((noreturn)) exit(int code)
{
  // assert GPIO[2]: main is finished
  // assert GPIO[3]: main return value is non zero
  gpioSetDirection(3, kGpioOutputDirection);
  gpioSetDirection(2, kGpioOutputDirection);
  gpioSetOutput(3, code == 0 ? kGpioOutputLow : kGpioOutputHigh);
  gpioSetOutput(2, kGpioOutputHigh);

  while (1) {
   // reduce activity in the CPU: less power used, faster simulation
    asm("wfi");
  }
}
