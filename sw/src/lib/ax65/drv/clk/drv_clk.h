#pragma once

/*
 * trivial clock "driver"
 * This is currently only used to provide the clock frequency for the UART
 * driver. It should be converted into a proper clock driver based on the clock
 * tree, once available.
 */

// helper macros
#define MHz(x) ((x) * 1000000ULL)
// reference clock frequency
#define CLK_REF_Hz MHz(50)

// allow overriding SOC_PERIPH frequency (required for Skyray FPGA)
#ifndef CLK_SOC_PERIPH_Hz
#define CLK_SOC_PERIPH_Hz CLK_REF_Hz
#endif
