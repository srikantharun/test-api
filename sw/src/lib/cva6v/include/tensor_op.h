// Description: Tensor operations header
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>
#include <dlpack.h>

#define TENSOR_FORMAT_NHWC 0
#define TENSOR_FORMAT_NCHW 1

#define FLOAT16_ERROR 0.005f
#define FLOAT_ERROR   0.000005f

#ifndef VERBOSE
#define VERBOSE 0
#endif

// Print float32 tensor to console for debugging
// Format can either be TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW
void print_tensor_float32(float *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format);

// Print float16 tensor to console for debugging
// Format can either be TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW
void print_tensor_float16(_Float16 *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format);

// Print uint8 tensor to console for debugging
// Format can either be TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW
void print_tensor_uint8(uint8_t *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format);

// Print int8 tensor to console for debugging
// Format can either be TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW
void print_tensor_int8(int8_t *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format);

// Print int32 tensor to console for debugging
// Format can either be TENSOR_FORMAT_NHWC or TENSOR_FORMAT_NCHW
void print_tensor_int32(int32_t *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format);

// Initialize empty input tensor
// The initialization will follow the following pattern:
// > matrix(i,j,k,l) = s_a*ni + s_b*hj + s_c*wk + s_d*cl + s_e
void init_tensor_float16(_Float16 *matrix, uint32_t n, uint32_t h, uint32_t w, uint32_t c, _Float16 s_a, _Float16 s_b,
                         _Float16 s_c, _Float16 s_d, _Float16 s_e, uint32_t format);

// Initialize empty input tensor
// The initialization will follow the following pattern:
// > matrix(i,j,k,l) = s_a*ni + s_b*hj + s_c*wk + s_d*cl + s_e
void init_tensor_uint8(uint8_t *matrix, uint32_t n, uint32_t h, uint32_t w, uint32_t c, uint8_t s_a, uint8_t s_b,
                       uint8_t s_c, uint8_t s_d, uint8_t s_e, uint32_t format);

// Initialize empty input tensor
// The initialization will follow the following pattern:
// > matrix(i,j,k,l) = s_a*ni + s_b*hj + s_c*wk + s_d*cl + s_e
void init_tensor_int8(int8_t *matrix, int32_t n, uint32_t h, uint32_t w, uint32_t c, int8_t s_a, int8_t s_b, int8_t s_c,
                      int8_t s_d, int8_t s_e, uint32_t format);

// Compare two float tensors of same size for equality
// The float error can explicitely be specified as a
// percentage of difference
int compare_tensors_float_with_error_percentage(float *golden, float *tensor, uint32_t n, uint32_t h, uint32_t w,
                                                uint32_t c, float error);

// Compare two float tensors of same size for equality
// The float error can explicitely be specified
int compare_tensors_float_with_error(float *golden, float *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                     float error);

// Compare two float tensors of same size for equality
// This uses the standard FLOAT16_ERROR
int compare_tensors_float(float *golden, float *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Compare two float16 tensors of same size for equality
// The float16 error can explicitely be specified as a
// percentage of difference
int compare_tensors_float16_with_error_percentage(_Float16 *golden, _Float16 *tensor, uint32_t n, uint32_t h,
                                                  uint32_t w, uint32_t c, _Float16 error);

// Compare two float16 tensors of same size for equality
// The float16 error can explicitely be specified
int compare_tensors_float16_with_error(_Float16 *golden, _Float16 *tensor, uint32_t n, uint32_t h, uint32_t w,
                                       uint32_t c, _Float16 error);

// Compare two float16 tensors of same size for equality
// This uses the standard FLOAT16_ERROR
int compare_tensors_float16(_Float16 *golden, _Float16 *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Compare two uint8 tensors of same size for similarity
// The maximum tolerable error (i.e., difference from the golden tensor) can be
// specified
int compare_tensors_uint8_with_error(uint8_t *golden, uint8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                     uint8_t error);

// Compare two uint8 tensors of same size for equality
int compare_tensors_uint8(uint8_t *golden, uint8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Compare two uint32 tensors of same size for similarity
// The maximum tolerable error (i.e., difference from the golden tensor) can be
// specified
int compare_tensors_uint32_with_error(uint32_t *golden, uint32_t *tensor, uint32_t n, uint32_t h, uint32_t w,
                                      uint32_t c, uint32_t error);

// Compare two uint32 tensors of same size for equality
int compare_tensors_uint32(uint32_t *golden, uint32_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Compare two int8 tensors of same size for similarity
// The maximum tolerable error (i.e., difference from the golden tensor) can be
// specified
int compare_tensors_int8_with_error(int8_t *golden, int8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                    uint8_t error);

// Compare two int8 tensors of same size for equality
int compare_tensors_int8(int8_t *golden, int8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Compare two int32 tensors of same size for similarity
// The maximum tolerable error (i.e., difference from the golden tensor) can be
// specified
int compare_tensors_int32_with_error(int32_t *golden, int32_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                     uint32_t error);

// Compare two int32 tensors of same size for equality
int compare_tensors_int32(int32_t *golden, int32_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Compare two DLTensors for equality (type, shape, and data)
int compare_dltensors(DLTensor *golden, DLTensor *tensor);

// Compare two DLTensors for similarity (same type, same shape, and data with maximum tolerable error)
int compare_dltensors_with_error(DLTensor *golden, DLTensor *tensor, float error);

// Compare two DLTensors for similarity (same type, same shape, and data with maximum tolerable percentage of
// difference)
int compare_dltensors_with_error_percentage(DLTensor *golden, DLTensor *tensor, float error);

// Copy data of a float16 tensor to another location
void copy_tensor_float16(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Copy data of a int8_t tensor to another location
void copy_tensor_int8(int8_t *src, int8_t *dst, uint32_t n, uint32_t h, uint32_t w, uint32_t c);

// Copy data of a uint8_t tensor to another location
void copy_tensor_uint8(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t h, uint32_t w, uint32_t c);
