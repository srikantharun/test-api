#include "drv_gpio.h"
#include <interrupt.h>
#include <memorymap.h>
#include <platform.h>
#include <std/std_basetype.h>
#include <std/std_bit.h>
#include <testutils.h>

#define DW_GPIO_INTEN_ENABLE 0xffff
#define DW_GPIO_INTMASK_UNMASK 0x0
#define DW_GPIO_INTTYPE_EDGE 0xffff
#define DW_GPIO_INTPOL_HIGH 0xffff

typedef struct {
  reg32_t swporta_dr;    // 0x000
  reg32_t swporta_ddr;   // 0x004
  reg32_t reserved0[10]; // 0x008
  reg32_t inten;         // 0x030
  reg32_t intmask;       // 0x034
  reg32_t inttype_level; // 0x038
  reg32_t int_polarity;  // 0x03c
  reg32_t intstatus;     // 0x040
  reg32_t raw_intstatus; // 0x044
  reg32_t reserved;      // 0x048
  reg32_t porta_eoi;     // 0x04c
  reg32_t ext_porta;     // 0x050
} HalGpioReg;

//! the pointer to the GPIO register file
#define pGPIO ((HalGpioReg *)(SOC_PERIPH_GPIO_BASE))

gpio_isr_func_pins_t callbackFunction[DW_GPIO_PWIDTH_A] = {NULL};
int registerGpioCallback(uint32_t pin, gpio_isr_func_pins_t cb) {
  callbackFunction[pin] = cb;

  return 0;
}

int deregisterGpioCallback(uint32_t pin) {
  callbackFunction[pin] = NULL;

  return 0;
}

void gpioSetDirection(uint32_t pin, gpioDirection direction) {
  ASSERT(pin < DW_GPIO_PWIDTH_A);
  if (direction == kGpioInputDirection) {
    pGPIO->swporta_ddr = stdBitClearU32(pGPIO->swporta_ddr, pin);
  } else {
    pGPIO->swporta_ddr = stdBitSetU32(pGPIO->swporta_ddr, pin);
  }
}

void gpioSetOutput(uint32_t pin, gpioOutput output) {
  ASSERT(pin < DW_GPIO_PWIDTH_A);
  if (output == kGpioOutputLow) {
    pGPIO->swporta_dr = stdBitClearU32(pGPIO->swporta_dr, pin);
  } else {
    pGPIO->swporta_dr = stdBitSetU32(pGPIO->swporta_dr, pin);
  }
}

int gpioReadInput(uint32_t pin) {
  ASSERT(pin < DW_GPIO_PWIDTH_A);
  return (pGPIO->ext_porta & STD_BIT32(pin)) != 0;
}

// Overrides the default gpio handler
void gpio_irq_handler(void) {
  uint32_t pin;
  uint32_t intstatus;

  // clear active GPIOs interrupt
  intstatus = pGPIO->intstatus & pGPIO->inten;
  pGPIO->porta_eoi = intstatus;

  for (pin = 0; pin < DW_GPIO_PWIDTH_A; pin++) {
    if (intstatus & 0x1) {
      /* Call GPIO specific irq_handler */
      if (callbackFunction[pin] != NULL) {
        callbackFunction[pin]();
      }
    }
    intstatus >>= 1;
  }
}

void gpioSetupInterrupt(void) {
#ifndef NO_INTERRUPTS
  HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_GPIO_SOURCE);
  HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_GPIO_SOURCE, IRQ_PRIORITY_DEFAULT);
#endif

  pGPIO->int_polarity = DW_GPIO_INTPOL_HIGH;
  pGPIO->inttype_level = DW_GPIO_INTTYPE_EDGE;
  pGPIO->intmask = DW_GPIO_INTMASK_UNMASK;
  pGPIO->inten = DW_GPIO_INTEN_ENABLE;
}
