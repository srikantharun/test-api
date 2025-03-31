// Description: Header file for softmax kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

#define X_DIMENSION 0
#define Y_DIMENSION 1

// Apply softmax activation function a vector or matrix.
// This function will override the original input tensor
// with the new values.
// Dim can either be X_DIMENSION or Y_DIMENSION
void softmax(_Float16 *matrix, uint32_t w, uint32_t h, uint32_t dim);
void softmax_xdim(_Float16 *matrix, uint32_t w, uint32_t h);
void softmax_ydim(_Float16 *matrix, uint32_t w, uint32_t h);

// Apply softmax activation function a vector or matrix.
// This function will override the original input tensor
// with the new values.
// Dim can either be X_DIMENSION or Y_DIMENSION
void softmax_rvv(_Float16 *matrix, uint32_t w, uint32_t h, uint32_t dim);
void softmax_xdim_rvv(_Float16 *matrix, uint32_t w, uint32_t h);
void softmax_ydim_rvv(_Float16 *matrix, uint32_t w, uint32_t h);
