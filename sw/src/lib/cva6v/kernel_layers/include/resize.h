// Description: Header file for resize kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

enum interpolation_mode { BILINEAR };

///////////
// Sclar //
///////////

/// Resize src image to new size using specific interpolation algorithm
///
/// @param[in] src input image of size `c_cnt * h_src * w_src`
/// @param[out] dst resized image of size `c_cnt * h_dst * w_dst`
/// @param[in] w_src input image width
/// @param[in] h_src input image height
/// @param[in] w_dst output image width
/// @param[in] h_dst output image height
/// @param[in] c_cnt image channel count
/// @param[in] tensor_format format of the input image (TENSOR_FORMAT_NCHW or TENSOR_FORMAT_NHWC)
/// @param[in] interpolation interpolation mode to use
int resize_float16(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst, uint32_t h_dst,
                   uint32_t c_cnt, uint32_t tensor_format, enum interpolation_mode interpolation);

/// Resize src image to new size using bilinear interpolation algorithm
///
/// @param[in] src input image of size `c_cnt * h_src * w_src`
/// @param[out] dst resized image of size `c_cnt * h_dst * w_dst`
/// @param[in] w_src input image width
/// @param[in] h_src input image height
/// @param[in] w_dst output image width
/// @param[in] h_dst output image height
/// @param[in] c_cnt image channel count
/// @param[in] format format of the input image (TENSOR_FORMAT_NCHW or TENSOR_FORMAT_NHWC)
void bilinear_interpolation_float16(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst,
                                    uint32_t h_dst, uint32_t c_cnt, uint32_t format);

/////////
// RVV //
/////////

/// Resize src image to new size using specific interpolation algorithm
///
/// @param[in] src input image of size `c_cnt * h_src * w_src`
/// @param[out] dst resized image of size `c_cnt * h_dst * w_dst`
/// @param[in] w_src input image width
/// @param[in] h_src input image height
/// @param[in] w_dst output image width
/// @param[in] h_dst output image height
/// @param[in] c_cnt image channel count
/// @param[in] tensor_format format of the input image (TENSOR_FORMAT_NCHW or TENSOR_FORMAT_NHWC)
/// @param[in] interpolation interpolation mode to use
int resize_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst, uint32_t h_dst,
                       uint32_t c_cnt, uint32_t tensor_format, enum interpolation_mode interpolation);

/// Resize src image to new size using bilinear interpolation algorithm
///
/// @param[in] src input image of size `c_cnt * h_src * w_src`
/// @param[out] dst resized image of size `c_cnt * h_dst * w_dst`
/// @param[in] w_src input image width
/// @param[in] h_src input image height
/// @param[in] w_dst output image width
/// @param[in] h_dst output image height
/// @param[in] c_cnt image channel count
/// @param[in] format format of the input image (TENSOR_FORMAT_NCHW or TENSOR_FORMAT_NHWC)
void bilinear_interpolation_float16_rvv(_Float16 *src, _Float16 *dst, uint32_t w_src, uint32_t h_src, uint32_t w_dst,
                                        uint32_t h_dst, uint32_t c_cnt, uint32_t format);
