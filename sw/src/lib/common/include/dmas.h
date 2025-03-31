// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***

#pragma once

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

struct DmaRegion {
  /* Base address */
  uintptr_t base;
  /* Region name */
  const char* name;
};

extern const struct DmaRegion dma_regions[];

const char * get_dma_name(uintptr_t address);
uintptr_t get_dma_base_addr(const char* name);
