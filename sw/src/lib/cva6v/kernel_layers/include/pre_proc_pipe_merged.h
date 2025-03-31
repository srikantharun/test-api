// Description: Header file for merged preprocessing pipeline kernel
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#pragma once

////////////
// Scalar //
////////////

/// Full image pre-processing pipeling with all operations merged to
/// reduce the load and store overhead.
/// This kernel takes an fp16 HWC formatted input image, resizes it down
/// and applies a center crop. The values are then normalized and the result
/// is reshaped to a CHW formatted output tensor.
///
/// @param[in] image input image (HWC) of size `input_h * input_w * 3 channels`
/// @param[out] output pre-processed image (CHW)
/// @param[in] image_w width of input image
/// @param[in] image_h height of input image
/// @param[in] resize_w width of resized image
/// @param[in] resize_h height of resized image
/// @param[in] crop_w width of cropped image
/// @param[in] crop_h height of cropped image
/// @param[in] norm_mean normalization mean values for each channel (3x)
/// @param[in] norm_std normalization standard deviation values for each channel (3x)
int pre_proc_pipe_merged(_Float16 *image, _Float16 *output, uint32_t image_w, uint32_t image_h, uint32_t resize_w,
                         uint32_t resize_h, uint32_t crop_w, uint32_t crop_h, _Float16 *norm_mean, _Float16 *norm_std);

/////////
// RVV //
/////////

/// Full image pre-processing pipeling with all operations merged to
/// reduce the load and store overhead.
/// This kernel takes an fp16 HWC formatted input image, resizes it down
/// and applies a center crop. The values are then normalized and the result
/// is reshaped to a CHW formatted output tensor.
///
/// @param[in] image input image (HWC) of size `input_h * input_w * 3 channels`
/// @param[out] output pre-processed image (CHW)
/// @param[in] image_w width of input image
/// @param[in] image_h height of input image
/// @param[in] resize_w width of resized image
/// @param[in] resize_h height of resized image
/// @param[in] crop_w width of cropped image
/// @param[in] crop_h height of cropped image
/// @param[in] norm_mean normalization mean values for each channel (3x)
/// @param[in] norm_std normalization standard deviation values for each channel (3x)
int pre_proc_pipe_merged_rvv(_Float16 *image, _Float16 *output, uint32_t image_w, uint32_t image_h, uint32_t resize_w,
                             uint32_t resize_h, uint32_t crop_w, uint32_t crop_h, _Float16 *norm_mean,
                             _Float16 *norm_std);
