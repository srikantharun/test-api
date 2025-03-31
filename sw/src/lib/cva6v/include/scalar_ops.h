// Description: Scalar operations header
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

/// Calculation of next power of two.
/// e.g. 123 -> 128
///
/// @param[in] VAL scalar value to find next power of two
/// @return value of next power of two
#define CEIL_POW2(VAL)  \
  ({                    \
    uint32_t tmp = VAL; \
    tmp--;              \
    tmp |= tmp >> 1;    \
    tmp |= tmp >> 2;    \
    tmp |= tmp >> 4;    \
    tmp |= tmp >> 8;    \
    tmp |= tmp >> 16;   \
    tmp++;              \
    tmp;                \
  })
