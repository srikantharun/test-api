// Description: Floating-point matmul kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <matmul_float.h>
#include <stdint.h>

#define MIN(a, b) ((a) < (b) ? (a) : (b))

// Matmul kernel C=AB
void matmul_f32(float *a, float *b, float *c, int32_t m_dim, int32_t n_dim, int32_t p_dim) {
  for (int32_t i = 0; i < m_dim; ++i) {
    for (int32_t j = 0; j < p_dim; ++j) {
      for (int32_t k = 0; k < n_dim; ++k) {
        c[i * p_dim + j] += a[i * n_dim + k] * b[k * p_dim + j];
      }
    }
  }
}

void matmul_f16(_Float16 *a, _Float16 *b, _Float16 *c, int32_t m_dim, int32_t n_dim, int32_t p_dim) {
  for (int32_t i = 0; i < m_dim; ++i) {
    for (int32_t j = 0; j < p_dim; ++j) {
      for (int32_t k = 0; k < n_dim; ++k) {
        c[i * p_dim + j] += a[i * n_dim + k] * b[k * p_dim + j];
      }
    }
  }
}

void matmul_rvv_f32(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                    const unsigned long int P) {
  if (M < 4) {
    matmul_rvv_f32_2xVL(c, a, b, M, N, P);
  } else if (M < 8) {
    matmul_rvv_f32_4xVL(c, a, b, M, N, P);
  } else {
    matmul_rvv_f32_8xVL(c, a, b, M, N, P);
  }
}

// ---------------
// 2xVL
// ---------------

void matmul_rvv_f32_2xVL(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                         const unsigned long int P) {
  // We work on 2 rows of the matrix at once
  const unsigned long int block_size = 2;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e32, m8, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    float *b_ = (float *)b + p;
    float *c_ = c + p;

    asm volatile("vsetvli zero, %0, e32, m8, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      float *a_ = (float *)a + m * N;

      // Prefetch two rows of matrix B
      float *b__ = b_;
      asm volatile("vle32.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle32.v v24, (%0);" ::"r"(b__));
      b__ += P;

      float *c__ = c_ + m * P;

      // Temporary variables
      float t0, t1;

      // Original pointer
      float *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vfmul.vf v0, v16, %0" ::"f"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vfmul.vf v8, v16, %0" ::"f"(t1));
      t1 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v24" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v24" ::"f"(t1));
        t1 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v24, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v16" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v16" ::"f"(t1));
        t1 = *a__;
      }

      // Last iteration: store results
      asm volatile("vfmacc.vf v0, %0, v24" ::"f"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v8, %0, v24" ::"f"(t1));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 4xVL
// ---------------

void matmul_rvv_f32_4xVL(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                         const unsigned long int P) {
  // We work on 4 rows of the matrix at once
  const unsigned long int block_size = 4;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    float *b_ = (float *)b + p;
    float *c_ = c + p;

    asm volatile("vsetvli zero, %0, e32, m4, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      float *a_ = (float *)a + m * N;

      // Prefetch two rows of matrix B
      float *b__ = b_;
      asm volatile("vle32.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle32.v v20, (%0);" ::"r"(b__));
      b__ += P;

      float *c__ = c_ + m * P;

      // Temporary variables
      float t0, t1, t2, t3;

      // Original pointer
      float *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1 = *a__, a__ += N;
      t2 = *a__, a__ += N;
      t3  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vfmul.vf v0, v16, %0" ::"f"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vfmul.vf v4, v16, %0" ::"f"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vfmul.vf v8, v16, %0" ::"f"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vfmul.vf v12, v16, %0" ::"f"(t3));
      t3 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t3));
        t3 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v16" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v16" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v16" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v16" ::"f"(t3));
        t3 = *a__;
      }

      // Last iteration: store results
      asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t1));
      asm volatile("vse32.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t2));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t3));
      asm volatile("vse32.v v12, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 8xVL
// ---------------

void matmul_rvv_f32_8xVL(float *c, const float *a, const float *b, const unsigned long int M, const unsigned long int N,
                         const unsigned long int P) {
  // We work on 8 rows of the matrix at once
  const unsigned long int block_size = 8;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e32, m2, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    float *b_ = (float *)b + p;
    float *c_ = c + p;

    asm volatile("vsetvli zero, %0, e32, m2, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      float *a_ = (float *)a + m * N;

      // Prefetch two rows of matrix B
      float *b__ = b_;
      asm volatile("vle32.v v18, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle32.v v20, (%0);" ::"r"(b__));
      b__ += P;

      float *c__ = c_ + m * P;

      // Temporary variables
      float t0, t1, t2, t3, t4, t5, t6, t7;

      // Original pointer
      float *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1 = *a__, a__ += N;
      t2 = *a__, a__ += N;
      t3 = *a__, a__ += N;
      t4 = *a__, a__ += N;
      t5 = *a__, a__ += N;
      t6 = *a__, a__ += N;
      t7  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vfmul.vf v0, v18, %0" ::"f"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vfmul.vf v2, v18, %0" ::"f"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vfmul.vf v4, v18, %0" ::"f"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vfmul.vf v6, v18, %0" ::"f"(t3));
      t3 = *a__, a__ += N;
      asm volatile("vfmul.vf v8, v18, %0" ::"f"(t4));
      t4 = *a__, a__ += N;
      asm volatile("vfmul.vf v10, v18, %0" ::"f"(t5));
      t5 = *a__, a__ += N;
      asm volatile("vfmul.vf v12, v18, %0" ::"f"(t6));
      t6 = *a__, a__ += N;
      asm volatile("vfmul.vf v14, v18, %0" ::"f"(t7));
      t7 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v18, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v2, %0, v20" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v6, %0, v20" ::"f"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vfmacc.vf v10, %0, v20" ::"f"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vfmacc.vf v14, %0, v20" ::"f"(t7));
        t7 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v18" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v2, %0, v18" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v18" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v6, %0, v18" ::"f"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v18" ::"f"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vfmacc.vf v10, %0, v18" ::"f"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v18" ::"f"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vfmacc.vf v14, %0, v18" ::"f"(t7));
        t7 = *a__;
      }

      // Last iteration: store results
      asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v2, %0, v20" ::"f"(t1));
      asm volatile("vse32.v v2, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t2));
      asm volatile("vse32.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v6, %0, v20" ::"f"(t3));
      asm volatile("vse32.v v6, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t4));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v10, %0, v20" ::"f"(t5));
      asm volatile("vse32.v v10, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t6));
      asm volatile("vse32.v v12, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v14, %0, v20" ::"f"(t7));
      asm volatile("vse32.v v14, (%0);" ::"r"(c__));
    }
  }
}

void matmul_rvv_f16(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                    const unsigned long int N, const unsigned long int P) {
  if (M < 4) {
    matmul_rvv_f16_2xVL(c, a, b, M, N, P);
  } else if (M < 8) {
    matmul_rvv_f16_4xVL(c, a, b, M, N, P);
  } else {
    matmul_rvv_f16_8xVL(c, a, b, M, N, P);
  }
}

// ---------------
// 2xVL
// ---------------

void matmul_rvv_f16_2xVL(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P) {
  // We work on 2 rows of the matrix at once
  const unsigned long int block_size = 2;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e16, m8, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    _Float16 *b_ = (_Float16 *)b + p;
    _Float16 *c_ = c + p;

    asm volatile("vsetvli zero, %0, e16, m8, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      _Float16 *a_ = (_Float16 *)a + m * N;

      // Prefetch two rows of matrix B
      _Float16 *b__ = b_;
      asm volatile("vle16.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle16.v v24, (%0);" ::"r"(b__));
      b__ += P;

      _Float16 *c__ = c_ + m * P;

      // Temporary variables
      _Float16 t0, t1;

      // Original pointer
      _Float16 *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vfmul.vf v0, v16, %0" ::"f"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vfmul.vf v8, v16, %0" ::"f"(t1));
      t1 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle16.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v24" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v24" ::"f"(t1));
        t1 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle16.v v24, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v16" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v16" ::"f"(t1));
        t1 = *a__;
      }

      // Last iteration: store results
      asm volatile("vfmacc.vf v0, %0, v24" ::"f"(t0));
      asm volatile("vse16.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v8, %0, v24" ::"f"(t1));
      asm volatile("vse16.v v8, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 4xVL
// ---------------

void matmul_rvv_f16_4xVL(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P) {
  // We work on 4 rows of the matrix at once
  const unsigned long int block_size = 4;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e16, m4, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    _Float16 *b_ = (_Float16 *)b + p;
    _Float16 *c_ = c + p;

    asm volatile("vsetvli zero, %0, e16, m4, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      _Float16 *a_ = (_Float16 *)a + m * N;

      // Prefetch two rows of matrix B
      _Float16 *b__ = b_;
      asm volatile("vle16.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle16.v v20, (%0);" ::"r"(b__));
      b__ += P;

      _Float16 *c__ = c_ + m * P;

      // Temporary variables
      _Float16 t0, t1, t2, t3;

      // Original pointer
      _Float16 *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1 = *a__, a__ += N;
      t2 = *a__, a__ += N;
      t3  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vfmul.vf v0, v16, %0" ::"f"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vfmul.vf v4, v16, %0" ::"f"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vfmul.vf v8, v16, %0" ::"f"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vfmul.vf v12, v16, %0" ::"f"(t3));
      t3 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle16.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t3));
        t3 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle16.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v16" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v16" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v16" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v16" ::"f"(t3));
        t3 = *a__;
      }

      // Last iteration: store results
      asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
      asm volatile("vse16.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t1));
      asm volatile("vse16.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t2));
      asm volatile("vse16.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t3));
      asm volatile("vse16.v v12, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 8xVL
// ---------------

void matmul_rvv_f16_8xVL(_Float16 *c, const _Float16 *a, const _Float16 *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P) {
  // We work on 8 rows of the matrix at once
  const unsigned long int block_size = 8;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e16, m2, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    _Float16 *b_ = (_Float16 *)b + p;
    _Float16 *c_ = c + p;

    asm volatile("vsetvli zero, %0, e16, m2, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      _Float16 *a_ = (_Float16 *)a + m * N;

      // Prefetch two rows of matrix B
      _Float16 *b__ = b_;
      asm volatile("vle16.v v18, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle16.v v20, (%0);" ::"r"(b__));
      b__ += P;

      _Float16 *c__ = c_ + m * P;

      // Temporary variables
      _Float16 t0, t1, t2, t3, t4, t5, t6, t7;

      // Original pointer
      _Float16 *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1 = *a__, a__ += N;
      t2 = *a__, a__ += N;
      t3 = *a__, a__ += N;
      t4 = *a__, a__ += N;
      t5 = *a__, a__ += N;
      t6 = *a__, a__ += N;
      t7  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vfmul.vf v0, v18, %0" ::"f"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vfmul.vf v2, v18, %0" ::"f"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vfmul.vf v4, v18, %0" ::"f"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vfmul.vf v6, v18, %0" ::"f"(t3));
      t3 = *a__, a__ += N;
      asm volatile("vfmul.vf v8, v18, %0" ::"f"(t4));
      t4 = *a__, a__ += N;
      asm volatile("vfmul.vf v10, v18, %0" ::"f"(t5));
      t5 = *a__, a__ += N;
      asm volatile("vfmul.vf v12, v18, %0" ::"f"(t6));
      t6 = *a__, a__ += N;
      asm volatile("vfmul.vf v14, v18, %0" ::"f"(t7));
      t7 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle16.v v18, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v2, %0, v20" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v6, %0, v20" ::"f"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vfmacc.vf v10, %0, v20" ::"f"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vfmacc.vf v14, %0, v20" ::"f"(t7));
        t7 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle16.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vfmacc.vf v0, %0, v18" ::"f"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vfmacc.vf v2, %0, v18" ::"f"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vfmacc.vf v4, %0, v18" ::"f"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vfmacc.vf v6, %0, v18" ::"f"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vfmacc.vf v8, %0, v18" ::"f"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vfmacc.vf v10, %0, v18" ::"f"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vfmacc.vf v12, %0, v18" ::"f"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vfmacc.vf v14, %0, v18" ::"f"(t7));
        t7 = *a__;
      }

      // Last iteration: store results
      asm volatile("vfmacc.vf v0, %0, v20" ::"f"(t0));
      asm volatile("vse16.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v2, %0, v20" ::"f"(t1));
      asm volatile("vse16.v v2, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v4, %0, v20" ::"f"(t2));
      asm volatile("vse16.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v6, %0, v20" ::"f"(t3));
      asm volatile("vse16.v v6, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v8, %0, v20" ::"f"(t4));
      asm volatile("vse16.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v10, %0, v20" ::"f"(t5));
      asm volatile("vse16.v v10, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v12, %0, v20" ::"f"(t6));
      asm volatile("vse16.v v12, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vfmacc.vf v14, %0, v20" ::"f"(t7));
      asm volatile("vse16.v v14, (%0);" ::"r"(c__));
    }
  }
}
