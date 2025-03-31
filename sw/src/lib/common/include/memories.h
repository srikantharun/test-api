// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Header for the auto-generated memories.c

#pragma once

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

struct MemoryRegion {
  /* Base address */
  uint64_t base;
  /* Size in bytes */
  size_t size;
  /* Region is readable */
  bool r;
  /* Region is writable */
  bool w;
  /* Region is executable */
  bool x;
  /* Region name */
  const char* name;
};

extern const struct MemoryRegion memory_regions[];

const char * get_memory_region_name(uintptr_t address);

