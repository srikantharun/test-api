// Description: Header file for floating-point matmul kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

// Calculates a simple matrix multiplication of:
// a: input matrix of size [m_dim x n_dim]
// b: input matrix of size [n_dim x p_dim]
// c: output matrix of size [m_dim x p_dim]
void matmul_f32(float *a, float *b, float *c, int32_t m_dim, int32_t n_dim, int32_t p_dim);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [m_dim x n_dim]
// b: input matrix of size [n_dim x p_dim]
// c: output matrix of size [m_dim x p_dim]
void matmul_f16(_Float16 *a, _Float16 *b, _Float16 *c, int32_t m_dim, int32_t n_dim, int32_t p_dim);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Minimum matrix size of [2 x 2] is required
void matmul_rvv_f32(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                    const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over two rows at a time
void matmul_rvv_f32_2xVL(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                         const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over four rows at a time
void matmul_rvv_f32_4xVL(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                         const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over eight rows at a time
void matmul_rvv_f32_8xVL(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                         const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Minimum matrix size of [2 x 2] is required
void matmul_rvv_f16(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                    const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over two rows at a time
void matmul_rvv_f16_2xVL(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over four rows at a time
void matmul_rvv_f16_4xVL(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over eight rows at a time
void matmul_rvv_f16_8xVL(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P);
