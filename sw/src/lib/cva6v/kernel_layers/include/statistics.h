// Description: Header file for statistics kernels
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

#define NORM_BATCH    0
#define NORM_LAYER    1
#define NORM_INSTANCE 2

#define EPSYLON 1.0E-5f

// Calculate the mean over the channels
// (NORM_BATCH), blocks (NORM_LAYERS), or channels and blocks (NORM_INSTANCE)
void mean(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, uint32_t format);

// Calculate the mean over the channels
// (NORM_BATCH), blocks (NORM_LAYERS), or channels and blocks (NORM_INSTANCE)
void mean_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, uint32_t format);

// Calculate the standard deviation over the channels
// (NORM_BATCH), blocks (NORM_LAYERS), or channels and blocks (NORM_INSTANCE)
void std(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std,
         uint32_t format);

// Calculate the standard deviation over the channels
// (NORM_BATCH), blocks (NORM_LAYERS), or channels and blocks (NORM_INSTANCE)
void std_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std,
             uint32_t format);

// Calculate the batch norm for each value in the input tensor.
// This operation happens in place. It will override the original tensor.
void batch_norm(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std);

// Calculate the batch norm for each value in the input tensor.
// This operation happens in place. It will override the original tensor.
void batch_norm_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std);

// Calculate the layer norm for each value in the input tensor.
// This operation happens in place. It will override the original tensor.
void layer_norm(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std);

// Calculate the layer norm for each value in the input tensor.
// This operation happens in place. It will override the original tensor.
void layer_norm_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std);

// Calculate the instance norm for each value in the input tensor.
// This operation happens in place. It will override the original tensor.
void instance_norm(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std);

// Calculate the instance norm for each value in the input tensor.
// This operation happens in place. It will override the original tensor.
void instance_norm_rvv(_Float16 *tensor, uint32_t n, uint32_t w, uint32_t h, uint32_t c, _Float16 *mean, _Float16 *std);
