// Description: Header file for gemm kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#pragma once

#include <stdint.h>

// hand-optimized i32 generalized matrix multiplication
// note: m must be a multiple of 16
void gemm_i32_rvv(unsigned long m, unsigned long n, unsigned long p,
                  const int32_t *A,  // m * n matrix
                  const int32_t *B,  // n * p matrix
                  int32_t       *C);       // m * p matrix
