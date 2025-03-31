#ifndef DW_GPIO_H
#define DW_GPIO_H

#include <stdint.h>
#define DW_GPIO_PWIDTH_A 16 // Number of pins instantiated in GPIOA

// 0 : Input Direction
// 1 : Output Direction
typedef enum {
  kGpioInputDirection = 0,
  kGpioOutputDirection = 1,
} gpioDirection;

// 0 : Drive Output Low
// 1 : Drive Output Low
typedef enum {
  kGpioOutputLow = 0,
  kGpioOutputHigh = 1,
} gpioOutput;

void gpioSetDirection(uint32_t pin, gpioDirection direction)
    __attribute__((section(".text.protected_exit"))) __attribute__((noinline));
void gpioSetOutput(uint32_t pin, gpioOutput output)
    __attribute__((section(".text.protected_exit"))) __attribute__((noinline));
int gpioReadInput(uint32_t pin) __attribute__((section(".text.protected_exit")))
__attribute__((noinline));
void gpioSetupInterrupt(void);

typedef void (*gpio_isr_func_pins_t)(void);
int registerGpioCallback(uint32_t pin, gpio_isr_func_pins_t cb);
int deregisterGpioCallback(uint32_t pin);

#endif // DW_GPIO_H
