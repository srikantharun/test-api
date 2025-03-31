// Description: Header file for conv2d kernels
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

// Non vectorized and filter size independant
// implementation of the 2d convolution.
// The input matrix is zero padded and contains
// a single channel.
void conv2d(int32_t *input_matrix, int32_t input_m_dim, int32_t input_n_dim, int32_t *filter_matrix, int32_t filter_dim,
            int32_t *output_matrix);

// Non vectorized and filter size independant
// implementation of the 2d convolution.
// The input matrix is zero padded and contains
// a single channel.
void conv2d_i8(int8_t *input_matrix, int32_t input_m_dim, int32_t input_n_dim, int8_t *filter_matrix,
               int32_t filter_dim, int8_t *output_matrix);

// Calculate a 2D convolution over theinput image (i)
// with a 3x3 filter. The input image has a single
// channel and is zero padded.
void conv2d_3x3(int32_t *o, int32_t *i, int32_t *f, int32_t num_rows, int32_t num_columns);

// Calculate a 2D convolution over theinput image (i)
// with a 3x3 filter. The input image has a single
// channel and is zero padded.
void conv2d_3x3_i8(int8_t *o, int8_t *i, int8_t *f, int32_t num_rows, int32_t num_columns);

// Calculate a 2D convolution over theinput image (i)
// with a 7x7 filter. The input image has a single
// channel and is zero padded.
void conv2d_7x7(int32_t *o, int32_t *i, int32_t *f, int32_t num_rows, int32_t num_columns);

// Calculate a 2D convolution over theinput image (i)
// with a 7x7 filter. The input image has a single
// channel and is zero padded.
void conv2d_7x7_i8(int8_t *o, int8_t *i, int8_t *f, int32_t num_rows, int32_t num_columns);
