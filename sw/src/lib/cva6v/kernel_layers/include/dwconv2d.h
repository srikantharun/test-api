// Description: Header file for dwconv2d kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

// Depth wise 2D convolution using fp32
// during requantization
//
// tensor: 8bit NCHW formatted input tensor
// filter: filter (weights) in CFF format
// output: 8bit NCHW formatted output tensor
//         of size N*C*(H-F+1)*(W-F+1)
//      a: requantization parameter (multiplication)
//      b: requantization parameter (addition)
void dwconv2d_fp32(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                   int8_t *output, float *a, float *b);

// Depth wise 2D convolution using fp16
// during requantization
//
// tensor: 8bit NCHW formatted input tensor
// filter: filter (weights) in CFF format
// output: 8bit NCHW formatted output tensor
//         of size N*C*(H-F+1)*(W-F+1)
//      a: requantization parameter (multiplication)
//      b: requantization parameter (addition)
//      q: quantization coefficient
void dwconv2d_fp16(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                   int8_t *output, _Float16 *a, _Float16 *b, int32_t *q);

// Vectorized depth wise 2D convolution
// using fp32 during requantization
//
// tensor: 8bit NCHW formatted input tensor
// filter: filter (weights) in CFF format
// output: 8bit NCHW formatted output tensor
//         of size N*C*(H-F+1)*(W-F+1)
//      a: requantization parameter (multiplication)
//      b: requantization parameter (addition)
void dwconv2d_fp32_rvv(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                       int8_t *output, float *a, float *b);

void dwconv2d_fp32_7xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            float *a, float *b);

void dwconv2d_fp32_3xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            float *a, float *b);

// Vectorized depth wise 2D convolution
// using fp16 during requantization
//
// tensor: 8bit NCHW formatted input tensor
// filter: filter (weights) in CFF format
// output: 8bit NCHW formatted output tensor
//         of size N*C*(H-F+1)*(W-F+1)
//      a: requantization parameter (multiplication)
//      b: requantization parameter (addition)
void dwconv2d_fp16_rvv(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                       int8_t *output, _Float16 *a, _Float16 *b, int32_t *q);

void dwconv2d_fp16_7xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            _Float16 *a, _Float16 *b, int32_t *q);

void dwconv2d_fp16_3xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            _Float16 *a, _Float16 *b, int32_t *q);
