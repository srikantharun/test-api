// Description: Header file for swish kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

// Applies the swish activation function to every element
// This operation is happens in-place and is matrix layout independant
void swish(_Float16 *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Applies the swish activation function to every element
// This operation is happens in-place and is matrix layout independant
void swish_rvv(_Float16 *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c);
