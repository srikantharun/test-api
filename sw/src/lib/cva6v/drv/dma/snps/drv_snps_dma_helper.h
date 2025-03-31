#pragma once

#include <std/std_basetype.h>
#include <stdint.h>
#include <memorymap.h>
#include <util.h>

// 8B  = 64b
#define DMAC_TR_WIDTH 8
#define DMAC_TR_WIDTH_SETTING SNPS_DMA_CTL_TR_WIDTH(64, 64)
