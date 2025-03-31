// Description: Header file for tensor conversion kernels
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

#define IMAGE_DEPTH_SCALE_INV 0.003921568627f

// Convert tensor from uint8 data format to float16
// Works with both NHWC and NCHW data arrangements
void tensor_uint8_to_float16(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Convert tensor from uint8 data format to float16
// Works with both NHWC and NCHW data arrangements
void tensor_uint8_to_float16_rvv(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Convert tensor from float16 data format to int8
// We take a round to even approach for ties, e.g.
// 2.5 -> 2, or 1.5 -> 2
// If there is an underflow or an underflow, the
// result will be cliped to INT8_MIN or INT8_MAX.
// Works with both NHWC and NCHW data arrangements
void tensor_float16_to_int8(_Float16 *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Convert tensor from float16 data format to int8
// We take a round to even approach for ties, e.g.
// 2.5 -> 2, or 1.5 -> 2
// If there is an underflow or an underflow, the
// result will be cliped to INT8_MIN or INT8_MAX.
// Works with both NHWC and NCHW data arrangements
void tensor_float16_to_int8_rvv(_Float16 *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Convert tensor from uint8 data format to float16
// and scale the values to be within [0.0, 1.0]
// Works with both NHWC and NCHW data arrangements
void tensor_uint8_to_float16_scaled(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Convert tensor from uint8 data format to float16
// and scale the values to be within [0.0, 1.0]
// Works with both NHWC and NCHW data arrangements
void tensor_uint8_to_float16_scaled_rvv(uint8_t *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Scale all values by scale factor
// Works with both NHWC and NCHW data arrangements
void tensor_float16_scaled(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c,
                           _Float16 scale);

// Scale the values by scale factor
// Works with both NHWC and NCHW data arrangements
void tensor_float16_scaled_rvv(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c,
                               _Float16 scale);

// Converts float16 tensor from NCHW data format to NHWC.
void tensor_format_nchw_to_nhwc_float16(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts float16 tensor from NCHW data format to NHWC.
void tensor_format_nchw_to_nhwc_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h,
                                            uint32_t c);

// Converts float16 tensor from NHWC data format to NCHW.
void tensor_format_nhwc_to_nchw_float16(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts float16 tensor from NHWC data format to NCHW.
void tensor_format_nhwc_to_nchw_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t w, uint32_t h,
                                            uint32_t c);

// Converts int8 tensor from NCHW data format to NHWC.
void tensor_format_nchw_to_nhwc_int8(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts int8 tensor from NCHW data format to NHWC.
void tensor_format_nchw_to_nhwc_int8_rvv(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts int8 tensor from NHWC data format to NCHW.
void tensor_format_nhwc_to_nchw_int8(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts int8 tensor from NHWC data format to NCHW.
void tensor_format_nhwc_to_nchw_int8_rvv(int8_t *src, int8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts uint8 tensor from NCHW data format to NHWC.
void tensor_format_nchw_to_nhwc_uint8(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts uint8 tensor from NCHW data format to NHWC.
void tensor_format_nchw_to_nhwc_uint8_rvv(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts uint8 tensor from NHWC data format to NCHW.
void tensor_format_nhwc_to_nchw_uint8(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);

// Converts uint8 tensor from NHWC data format to NCHW.
void tensor_format_nhwc_to_nchw_uint8_rvv(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t w, uint32_t h, uint32_t c);
