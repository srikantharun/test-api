// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#pragma once

#include <stdint.h>

// Set a bit in a uint32_t number
inline uint32_t stdBitSetU32(uint32_t n, uint32_t k) __attribute__((always_inline));
inline uint32_t stdBitSetU32(uint32_t n, uint32_t k) { return n | (((uint32_t)1) << (k)); }

// Clear a bit in a uint32_t number
inline uint32_t stdBitClearU32(uint32_t n, uint32_t k) __attribute__((always_inline));
inline uint32_t stdBitClearU32(uint32_t n, uint32_t k) { return n & (~(((uint32_t)1) << (k))); }

// Get a uint32_t bit
#define STD_BIT32(a) (((uint32_t)1) << (uint32_t)(a))

// Get a uint64_t bit
#define STD_BIT64(a) (((uint64_t)1) << (uint64_t)(a))

#define BIT_MASK(_offset, _width) (((1UL << (_width)) - 1UL) << (_offset))

#define BIT_READ_RANGE(_target, _offset, _width) \
  (((_target) >> (_offset)) & (((1UL) << (_width)) - (1UL)))
#define BIT_WRITE_RANGE(_target, _offset, _width, _value)        \
  ((_target) = (((_target) & ~(BIT_MASK((_offset), (_width)))) | \
                (((_value) << (_offset)) & (BIT_MASK((_offset), (_width))))))

// _target[_upper_bit : _lower_bit]
#define BIT_READ_SELECT(_target, _upper_bit, _lower_bit) \
  BIT_READ_RANGE(_target, _lower_bit, (_upper_bit - _lower_bit + 1))

#define BIT_SET_FLAG(_target, _offset) ((_target) |= (1UL << (_offset)))
#define BIT_CLEAR_FLAG(_target, _offset) ((_target) &= ~(1UL << (_offset)))
#define BIT_READ_FLAG(_target, _offset) ((_target) & (1UL << (_offset)))
#define BIT_CHECK_FLAG(_target, _offset) (((_target) & (1UL << (_offset))) == (1UL << (_offset)))

#define DP_BIT_READ_FIELD(_target, _field) (BIT_READ_RANGE((_target), _field##_OFFSET, _field##_WIDTH))
#define DP_BIT_WRITE_FIELD(_target, _field, _value) \
  (BIT_WRITE_RANGE((_target), _field##_OFFSET, _field##_WIDTH, (_value)))

#define DP_BIT_SET_FLAG(_target, _field) ((_target) |= (1UL << (_field##_OFFSET)))
#define DP_BIT_CLEAR_FLAG(_target, _field) ((_target) &= ~(1UL << (_field##_OFFSET)))
#define DP_BIT_READ_FLAG(_target, _field) ((_target) & (1UL << (_field##_OFFSET)))
#define DP_BIT_CHECK_FLAG(_target, _field) (((_target) & (1UL << (_field##_OFFSET))) == (1UL << (_field##_OFFSET)))

