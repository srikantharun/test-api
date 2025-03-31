// Description: Scalar conv2d kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <conv2d.h>
#include <stdint.h>

// Calculate the 2d convolution of a zero padded input matrix i and a filter
// matrix f
void conv2d(int32_t *input_matrix, int32_t input_m_dim, int32_t input_n_dim, int32_t *filter_matrix, int32_t filter_dim,
            int32_t *output_matrix) {
  int32_t padding = filter_dim / 2;

  for (int32_t m = 0; m < input_m_dim; m++) {
    for (int32_t n = 0; n < input_n_dim; n++) {
      int32_t o_idx        = m * input_n_dim + n;
      output_matrix[o_idx] = 0;

      for (int32_t fy = 0; fy < filter_dim; fy++) {
        int32_t m_ = m + fy;

        // #pragma clang loop __riscv_vectorize(enable)
        for (int32_t fx = 0; fx < filter_dim; fx++) {
          int32_t n_ = n + fx;

          int32_t i_idx = m_ * (input_n_dim + padding * 2) + n_;
          int32_t f_idx = fy * filter_dim + fx;

          output_matrix[o_idx] += input_matrix[i_idx] * filter_matrix[f_idx];
        }
      }
    }
  }
}

void conv2d_i8(int8_t *input_matrix, int32_t input_m_dim, int32_t input_n_dim, int8_t *filter_matrix,
               int32_t filter_dim, int8_t *output_matrix) {
  int32_t padding = filter_dim / 2;

  for (int32_t m = 0; m < input_m_dim; m++) {
    for (int32_t n = 0; n < input_n_dim; n++) {
      int32_t o_idx        = m * input_n_dim + n;
      output_matrix[o_idx] = 0;

      for (int32_t fy = 0; fy < filter_dim; fy++) {
        int32_t m_ = m + fy;

        // #pragma clang loop __riscv_vectorize(enable)
        for (int32_t fx = 0; fx < filter_dim; fx++) {
          int32_t n_ = n + fx;

          int32_t i_idx = m_ * (input_n_dim + padding * 2) + n_;
          int32_t f_idx = fy * filter_dim + fx;

          output_matrix[o_idx] += input_matrix[i_idx] * filter_matrix[f_idx];
        }
      }
    }
  }
}
