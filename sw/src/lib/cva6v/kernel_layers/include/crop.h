// Description: Header file for crop kernels
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>
#include <tensor_op.h>
#include <util.h>

////////////
// Scalar //
////////////

/// Crop a smaller image out of an input image.
/// Coordinate (0,0) is at the top left point. Crops
/// are relative to there.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] top_left_x starting point of crop (distance to image left side)
/// @param[in] top_left_y starting point of crop (distance to image top side)
/// @param[in] format tensor layour format (TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW)
int crop(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c, uint32_t crop_h,
         uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y, uint32_t format);

/// Crop a smaller image out of an input image.
/// The crop is centered to the input image and has equal
/// distances between top/bottom and right/left sides.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] format tensor layour format (TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW)
int center_crop(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                uint32_t crop_h, uint32_t crop_w, uint32_t format);

/// Crop a smaller image out of an input image.
/// Coordinate (0,0) is at the top left point. Crops
/// are relative to there.
/// The input image tensor is in a HWC format.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] top_left_x starting point of crop (distance to image left side)
/// @param[in] top_left_y starting point of crop (distance to image top side)
void image_crop_hwc(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                    uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y);

/// Crop a smaller image out of an input image.
/// Coordinate (0,0) is at the top left point. Crops
/// are relative to there.
/// The input image tensor is in a CHW format.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] top_left_x starting point of crop (distance to image left side)
/// @param[in] top_left_y starting point of crop (distance to image top side)
void image_crop_chw(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                    uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y);

/////////
// RVV //
/////////

/// Crop a smaller image out of an input image.
/// Coordinate (0,0) is at the top left point. Crops
/// are relative to there.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] top_left_x starting point of crop (distance to image left side)
/// @param[in] top_left_y starting point of crop (distance to image top side)
/// @param[in] format tensor layour format (TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW)
int crop_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c, uint32_t crop_h,
             uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y, uint32_t format);

/// Crop a smaller image out of an input image.
/// The crop is centered to the input image and has equal
/// distances between top/bottom and right/left sides.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] format tensor layour format (TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW)
int center_crop_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                    uint32_t crop_h, uint32_t crop_w, uint32_t format);

/// Crop a smaller image out of an input image.
/// Coordinate (0,0) is at the top left point. Crops
/// are relative to there.
/// The input image tensor is in a HWC format.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] top_left_x starting point of crop (distance to image left side)
/// @param[in] top_left_y starting point of crop (distance to image top side)
void image_crop_hwc_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                        uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y);

/// Crop a smaller image out of an input image.
/// Coordinate (0,0) is at the top left point. Crops
/// are relative to there.
/// The input image tensor is in a CHW format.
///
/// @param[in] image image to be cropped
/// @param[out] output image
/// @param[in] image_h height of input image
/// @param[in] image_w width of input image
/// @param[in] image_c number of channels in input image
/// @param[in] crop_h height of cropped image
/// @param[in] crop_w height of cropped image
/// @param[in] top_left_x starting point of crop (distance to image left side)
/// @param[in] top_left_y starting point of crop (distance to image top side)
void image_crop_chw_rvv(_Float16 *image, _Float16 *output, uint32_t image_h, uint32_t image_w, uint32_t image_c,
                        uint32_t crop_h, uint32_t crop_w, uint32_t top_left_x, uint32_t top_left_y);

