#pragma once

#include <std/std_basetype.h>
#include <stdint.h>
#include <memorymap.h>
#include <util.h>

// 32B = 256b
#define DMAC_TR_WIDTH 32
#define DMAC_TR_WIDTH_SETTING SNPS_DMA_CTL_TR_WIDTH(256, 256)
