#pragma once

#include <printf.h>
#include <stddef.h>
#include <stdint.h>
#include <clk/drv_clk.h>
#include <platform_common.h>

__attribute__((noreturn)) void exit(int code);
__attribute__((noreturn)) void abort();

/*****************************************************************************
 * Interrupts
 ****************************************************************************/
#include <platform_irqs.h>


/*****************************************************************************
 * SPI Device
 ****************************************************************************/
#define SPI_SER                  0
// bus_clk_rate needs to be at least twice as fast as the spi_speed
// and low enough so processor can read rx buffer before an overflow occurs
// the ration SPI_BUS_CLK_RATE/SPI_SPEED has to be at least
// cached: >=16
// unached: >=42
#define SPI_BUS_CLK_RATE   MHz(20)
#define CLK_DIVISION              64
#define SPI_SPEED          SPI_BUS_CLK_RATE / CLK_DIVISION
#define SPI_SCPOL                0
#define SPI_SCPH                 0
#define SPI_PLAT_APB             1
#define SPI_PLAT_DWC             0

#define IRQ_PRIORITY_DISABLED 0
#define IRQ_PRIORITY_DEFAULT 1

/*****************************************************************************
 * GPIO Pins
 ****************************************************************************/
#define GPIO_PIN_LOOPBACK_OUT  0
#define GPIO_PIN_LOOPBACK_IN   1
