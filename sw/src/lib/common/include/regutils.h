// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: definition of functions to read and write registers

#pragma once

#include <stdint.h>

inline __attribute__((always_inline)) void set_reg_u8(uintptr_t addr, uint8_t value)
{
    volatile uint8_t *loc_addr = (volatile uint8_t *)addr;
    *loc_addr = value;
}

inline __attribute__((always_inline)) uint8_t get_reg_u8(uintptr_t addr)
{
    return *(volatile uint8_t *)addr;
}

// RMW on a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) void set_range_u8_mask(uintptr_t addr, uint8_t value, uint8_t lower, uint8_t mask)
{
  uint8_t data = get_reg_u8(addr);
  mask = mask << lower;
  data = (data & ~mask) | ((value << lower) & mask);
  set_reg_u8(addr,data);
}

// RMW on a specific range of an external register (upper bit included)
inline __attribute__((always_inline)) void set_range_u8(uintptr_t addr, uint8_t value, uint8_t upper, uint8_t lower)
{
    uint8_t mask = (1 << (upper+1-lower)) - 1;
    set_range_u8_mask(addr, value, lower, mask);
}

// get only a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) uint8_t get_range_u8_mask(uintptr_t addr, uint8_t lower, uint8_t mask)
{
    uint8_t data = get_reg_u8(addr);
    mask = mask << lower;
    return (data & mask) >> lower;
}

// get only a specific range of an external register
inline __attribute__((always_inline)) uint8_t get_range_u8(uintptr_t addr, uint8_t upper, uint8_t lower)
{
    uint8_t mask = (1 << (upper+1-lower)) - 1;
    return get_range_u8_mask(addr, lower, mask);
}


inline __attribute__((always_inline)) void set_reg_u16(uintptr_t addr, uint16_t value)
{
    volatile uint16_t *loc_addr = (volatile uint16_t *)addr;
    *loc_addr = value;
}

inline __attribute__((always_inline)) uint16_t get_reg_u16(uintptr_t addr)
{
    return *(volatile uint16_t *)addr;
}

// RMW on a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) void set_range_u16_mask(uintptr_t addr, uint16_t value, uint16_t lower, uint16_t mask)
{
  uint16_t data = get_reg_u16(addr);
  mask = mask << lower;
  data = (data & ~mask) | ((value << lower) & mask);
  set_reg_u16(addr,data);
}

// RMW on a specific range of an external register (upper bit included)
inline __attribute__((always_inline)) void set_range_u16(uintptr_t addr, uint16_t value, uint16_t upper, uint16_t lower)
{
    uint16_t mask = (1 << (upper+1-lower)) - 1;
    set_range_u16_mask(addr, value, lower, mask);
}

// get only a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) uint16_t get_range_u16_mask(uintptr_t addr, uint16_t lower, uint16_t mask)
{
    uint16_t data = get_reg_u16(addr);
    mask = mask << lower;
    return (data & mask) >> lower;
}

// get only a specific range of an external register
inline __attribute__((always_inline)) uint16_t get_range_u16(uintptr_t addr, uint16_t upper, uint16_t lower)
{
    uint16_t mask = (1 << (upper+1-lower)) - 1;
    return get_range_u16_mask(addr, lower, mask);
}


inline __attribute__((always_inline)) void set_reg_u32(uintptr_t addr, uint32_t value)
{
    volatile uint32_t *loc_addr = (volatile uint32_t *)addr;
    *loc_addr = value;
}

inline __attribute__((always_inline)) uint32_t get_reg_u32(uintptr_t addr)
{
    return *(volatile uint32_t *)addr;
}

// RMW on a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) void set_range_u32_mask(uintptr_t addr, uint32_t value, uint32_t lower, uint32_t mask)
{
  uint32_t data = get_reg_u32(addr);
  mask = mask << lower;
  data = (data & ~mask) | ((value << lower) & mask);
  set_reg_u32(addr,data);
}

// RMW on a specific range of an external register (upper bit included)
inline __attribute__((always_inline)) void set_range_u32(uintptr_t addr, uint32_t value, uint32_t upper, uint32_t lower)
{
    uint32_t mask = (1 << (upper+1-lower)) - 1;
    set_range_u32_mask(addr, value, lower, mask);
}

// get only a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) uint32_t get_range_u32_mask(uintptr_t addr, uint32_t lower, uint32_t mask)
{
    uint32_t data = get_reg_u32(addr);
    mask = mask << lower;
    return (data & mask) >> lower;
}

// get only a specific range of an external register
inline __attribute__((always_inline)) uint32_t get_range_u32(uintptr_t addr, uint32_t upper, uint32_t lower)
{
    uint32_t mask = (1 << (upper+1-lower)) - 1;
    return get_range_u32_mask(addr, lower, mask);
}


inline __attribute__((always_inline)) void set_reg_u64(uintptr_t addr, uint64_t value)
{
    volatile uint64_t *loc_addr = (volatile uint64_t *)addr;
    *loc_addr = value;
}

inline __attribute__((always_inline)) uint64_t get_reg_u64(uintptr_t addr)
{
    return *(volatile uint64_t *)addr;
}

// RMW on a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) void set_range_u64_mask(uintptr_t addr, uint64_t value, uint64_t lower, uint64_t mask)
{
  uint64_t data = get_reg_u64(addr);
  mask = mask << lower;
  data = (data & ~mask) | ((value << lower) & mask);
  set_reg_u64(addr,data);
}

// RMW on a specific range of an external register (upper bit included)
inline __attribute__((always_inline)) void set_range_u64(uintptr_t addr, uint64_t value, uint64_t upper, uint64_t lower)
{
    uint64_t mask = (1 << (upper+1-lower)) - 1;
    set_range_u64_mask(addr, value, lower, mask);
}

// get only a specific range of an external register (bitmask and lower bit included)
inline __attribute__((always_inline)) uint64_t get_range_u64_mask(uintptr_t addr, uint64_t lower, uint64_t mask)
{
    uint64_t data = get_reg_u64(addr);
    mask = mask << lower;
    return (data & mask) >> lower;
}

// get only a specific range of an external register
inline __attribute__((always_inline)) uint64_t get_range_u64(uintptr_t addr, uint64_t upper, uint64_t lower)
{
    uint64_t mask = (1 << (upper+1-lower)) - 1;
    return get_range_u64_mask(addr, lower, mask);
}
