/*
 * Copyright (c) 2012-2021 Andes Technology Corporation
 * All rights reserved.
 *
 */

#include <encoding.h>
#include <interrupt.h>
#include <platform.h>
#include <pve_clint.h>
#include <testutils.h>
#include <dw_i2c/drv_i2c.h>
#include <cdns_emmc/drv_emmc.h>

void default_irq_handler(void) {
  while (1)
    ;
}

void uart_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));
void gpio_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));
void timer_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));
void decoder_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));
void spi_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));
void i2c0_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));
void i2c1_irq_handler(void) __attribute__((weak, alias("default_irq_handler")));

const isr_func irq_handler[NUM_IRQ_SOURCES] = {
    [0] = default_irq_handler, // Irq0 is hardwired to 0
    [IRQ_SOC_PERIPH_TIMER_SOURCE] = timer_irq_handler,
    [IRQ_DCD_INT_SOURCE] = decoder_irq_handler,
    [IRQ_SOC_PERIPH_UART_SOURCE] = uart_irq_handler,
    [IRQ_SOC_PERIPH_GPIO_SOURCE] = gpio_irq_handler,
    [IRQ_SOC_PERIPH_I2C_0_SOURCE] = i2c0_irq_handler,
    [IRQ_SOC_PERIPH_I2C_1_SOURCE] = i2c1_irq_handler,
    [IRQ_SOC_PERIPH_SPI_SOURCE] = spi_irq_handler,
    [IRQ_SOC_PERIPH_EMMC_SOURCE] = emmc_irq_handler,
};

__attribute__((weak)) void verify_interrupt(
    unsigned int irq_source) { /*Optionally override for verification*/
  UNUSED(irq_source);
}

__attribute__((weak)) void mext_interrupt(unsigned int irq_source) {
  ASSERT(irq_source < NUM_IRQ_SOURCES, "unknown IRQ received");

  /* Optionally verify interrupts for verification */
  verify_interrupt(irq_source);

  /* Do interrupt handler */
  irq_handler[irq_source]();

  __nds__plic_complete_interrupt(irq_source);
}

/* ========================================================================= */
/* core-local interupt handling (neither timer, PLIC, or SW PLIC interrupts) */
/* ========================================================================= */

/* default handlers for local interrupts (can be overriden if required) */
__attribute__((noreturn))
static void default_local_irq_handler(const char *local_irq_name) {
  printf("\r\n");
  printf("=== UNHANDLED LOCAL INTERRUPT ===\r\n");
  printf("%s\r\n", local_irq_name);
  printf("\r\n");
  printf("aborting...\r\n");

  uint64_t mcause = read_csr(mcause);
  exit((0b111 << 16) | mcause);
  while (1)
    ;
}

__attribute__((weak)) void local_irq_lcof_handler(void) {
  default_local_irq_handler("LCOF: local count overflow");
}

__attribute__((weak)) void local_irq_imecc_handler(void) {
  default_local_irq_handler("IMECC: imprecise ECC error");
}

__attribute__((weak)) void local_irq_bwe_handler(void) {
  default_local_irq_handler("BWE: bus read/write transaction error");
}

/* SW IRQs */
__attribute__((weak)) void mswi_handler(void) {
  ;
}

const isr_func sw_irq_handler[SW_IRQ_TOTAL] = {
    mswi_handler,
    mswi_handler,
    mswi_handler,
    mswi_handler,
    mswi_handler,
    mswi_handler,
};

__attribute__((weak)) void msw_interrupt(unsigned int irq_source) {
  /* Enable interrupts in general to allow nested */
  set_csr(NDS_MSTATUS, MSTATUS_MIE);

  /* Do interrupt handler */
  sw_irq_handler[irq_source]();

  __nds__plic_sw_complete_interrupt(irq_source);
}

void interrupt_core(tid_t hart_id) {
  if(hart_id < PVE_0_CLUSTER_0_CORE_0)
  {
    /* Call interrupt on SW PLIC */
    HAL_MSWI_PENDING(hart_id);
  } else {
    pve_clint_set_sw_irq(hart_id);
  }
}
