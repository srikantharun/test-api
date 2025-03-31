// Description: Header file for integer matmul kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

// Calculates a simple matrix multiplication of:
// a: input matrix of size [m_dim x n_dim]
// b: input matrix of size [n_dim x p_dim]
// c: output matrix of size [m_dim x p_dim]
void matmul_i32(int32_t *a, int32_t *b, int32_t *c, int32_t m_dim, int32_t n_dim, int32_t p_dim);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [m_dim x n_dim]
// b: input matrix of size [n_dim x p_dim]
// c: output matrix of size [m_dim x p_dim]
void matmul_i8(int8_t *a, int8_t *b, int8_t *c, int32_t m_dim, int32_t n_dim, int32_t p_dim);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Minimum matrix size of [2 x 2] is required
void matmul_rvv_i32(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                    const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over two rows at a time
void matmul_rvv_i32_2xVL(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over four rows at a time
void matmul_rvv_i32_4xVL(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over eight rows at a time
void matmul_rvv_i32_8xVL(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Minimum matrix size of [2 x 2] is required
void matmul_rvv_i8(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M, const unsigned long int N,
                   const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over two rows at a time
void matmul_rvv_i8_2xVL(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M,
                        const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over four rows at a time
void matmul_rvv_i8_4xVL(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M,
                        const unsigned long int N, const unsigned long int P);

// Calculates a simple matrix multiplication of:
// a: input matrix of size [M x N]
// b: input matrix of size [N x P]
// c: output matrix of size [M x P]
// Calculation happens over eight rows at a time
void matmul_rvv_i8_8xVL(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M,
                        const unsigned long int N, const unsigned long int P);
