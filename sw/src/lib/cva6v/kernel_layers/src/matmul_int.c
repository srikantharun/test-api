// Description: Integer matmul kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <matmul_int.h>
#include <stdint.h>

#define MIN(a, b) ((a) < (b) ? (a) : (b))

// Matmul kernel C=AB
void matmul_i32(int32_t *a, int32_t *b, int32_t *c, int32_t m_dim, int32_t n_dim, int32_t p_dim) {
  for (int32_t i = 0; i < m_dim; ++i) {
    for (int32_t j = 0; j < p_dim; ++j) {
      for (int32_t k = 0; k < n_dim; ++k) {
        c[i * p_dim + j] += a[i * n_dim + k] * b[k * p_dim + j];
      }
    }
  }
}

void matmul_i8(int8_t *a, int8_t *b, int8_t *c, int32_t m_dim, int32_t n_dim, int32_t p_dim) {
  for (int32_t i = 0; i < m_dim; ++i) {
    for (int32_t j = 0; j < p_dim; ++j) {
      for (int32_t k = 0; k < n_dim; ++k) {
        c[i * p_dim + j] += a[i * n_dim + k] * b[k * p_dim + j];
      }
    }
  }
}

void matmul_rvv_i32(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                    const unsigned long int N, const unsigned long int P) {
  if (M < 4) {
    matmul_rvv_i32_2xVL(c, a, b, M, N, P);
  } else if (M < 8) {
    matmul_rvv_i32_4xVL(c, a, b, M, N, P);
  } else {
    matmul_rvv_i32_8xVL(c, a, b, M, N, P);
  }
}

// ---------------
// 2x2
// ---------------

void matmul_rvv_i32_2xVL(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P) {
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
    int32_t *b_ = (int32_t *)b + p;
    int32_t *c_ = c + p;

    asm volatile("vsetvli zero, %0, e32, m8, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      int32_t *a_ = (int32_t *)a + m * N;

      // Prefetch one row of matrix B
      int32_t *b__ = b_;
      asm volatile("vle32.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle32.v v24, (%0);" ::"r"(b__));
      b__ += P;

      int32_t *c__ = c_ + m * P;

      // Temporary variables
      int32_t t0, t1;

      // Original pointer
      int32_t *a__ = a_;

      // Keept track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vmul.vx v0, v16, %0" ::"r"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vmul.vx v8, v16, %0" ::"r"(t1));
      t1 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v24" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v24" ::"r"(t1));
        t1 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v24, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v16" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v16" ::"r"(t1));
        t1 = *a__;
      }

      // Last iteration: store results
      asm volatile("vmacc.vx v0, %0, v24" ::"r"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v24" ::"r"(t1));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 4x4
// ---------------

void matmul_rvv_i32_4xVL(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P) {
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
    int32_t *b_ = (int32_t *)b + p;
    int32_t *c_ = c + p;

    asm volatile("vsetvli zero, %0, e32, m4, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      int32_t *a_ = (int32_t *)a + m * N;

      // Prefetch one row of matrix B
      int32_t *b__ = b_;
      asm volatile("vle32.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle32.v v20, (%0);" ::"r"(b__));
      b__ += P;

      int32_t *c__ = c_ + m * P;

      // Temporary variables
      int32_t t0, t1, t2, t3;

      // Original pointer
      int32_t *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1 = *a__, a__ += N;
      t2 = *a__, a__ += N;
      t3  = *a__;
      a__ = a_ + n++;

      asm volatile("vmul.vx v0, v16, %0" ::"r"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vmul.vx v4, v16, %0" ::"r"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vmul.vx v8, v16, %0" ::"r"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vmul.vx v12, v16, %0" ::"r"(t3));
      t3 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v20" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v20" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v20" ::"r"(t3));
        t3 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v16" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v16" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v16" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v16" ::"r"(t3));
        t3 = *a__;
      }

      // Last iteration: store results
      asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v4, %0, v20" ::"r"(t1));
      asm volatile("vse32.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v20" ::"r"(t2));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v12, %0, v20" ::"r"(t3));
      asm volatile("vse32.v v12, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 8x8
// ---------------

void matmul_rvv_i32_8xVL(int32_t *c, const int32_t *a, const int32_t *b, const unsigned long int M,
                         const unsigned long int N, const unsigned long int P) {
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
    int32_t *b_ = (int32_t *)b + p;
    int32_t *c_ = c + p;

    asm volatile("vsetvli zero, %0, e32, m2, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      int32_t *a_ = (int32_t *)a + m * N;

      // Prefetch one row of matrix B
      int32_t *b__ = b_;
      asm volatile("vle32.v v18, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle32.v v20, (%0);" ::"r"(b__));
      b__ += P;

      int32_t *c__ = c_ + m * P;

      // Temporary variables
      int32_t t0, t1, t2, t3, t4, t5, t6, t7;

      // Original pointer
      int32_t *a__ = a_;

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
      asm volatile("vmul.vx v0, v18, %0" ::"r"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vmul.vx v2, v18, %0" ::"r"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vmul.vx v4, v18, %0" ::"r"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vmul.vx v6, v18, %0" ::"r"(t3));
      t3 = *a__, a__ += N;
      asm volatile("vmul.vx v8, v18, %0" ::"r"(t4));
      t4 = *a__, a__ += N;
      asm volatile("vmul.vx v10, v18, %0" ::"r"(t5));
      t5 = *a__, a__ += N;
      asm volatile("vmul.vx v12, v18, %0" ::"r"(t6));
      t6 = *a__, a__ += N;
      asm volatile("vmul.vx v14, v18, %0" ::"r"(t7));
      t7 = *a__;

      // Compute the multiplication

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v18, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v2, %0, v20" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v20" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v6, %0, v20" ::"r"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v20" ::"r"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vmacc.vx v10, %0, v20" ::"r"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v20" ::"r"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vmacc.vx v14, %0, v20" ::"r"(t7));
        t7 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle32.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v18" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v2, %0, v18" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v18" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v6, %0, v18" ::"r"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v18" ::"r"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vmacc.vx v10, %0, v18" ::"r"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v18" ::"r"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vmacc.vx v14, %0, v18" ::"r"(t7));
        t7 = *a__;
      }

      // Last iteration: store results
      asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v2, %0, v20" ::"r"(t1));
      asm volatile("vse32.v v2, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v4, %0, v20" ::"r"(t2));
      asm volatile("vse32.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v6, %0, v20" ::"r"(t3));
      asm volatile("vse32.v v6, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v20" ::"r"(t4));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v10, %0, v20" ::"r"(t5));
      asm volatile("vse32.v v10, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v12, %0, v20" ::"r"(t6));
      asm volatile("vse32.v v12, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v14, %0, v20" ::"r"(t7));
      asm volatile("vse32.v v14, (%0);" ::"r"(c__));
    }
  }
}

void matmul_rvv_i8(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M, const unsigned long int N,
                   const unsigned long int P) {
  if (M < 4) {
    matmul_rvv_i8_2xVL(c, a, b, M, N, P);
  } else if (M < 8) {
    matmul_rvv_i8_4xVL(c, a, b, M, N, P);
  } else {
    matmul_rvv_i8_8xVL(c, a, b, M, N, P);
  }
}

// ---------------
// 2x2
// ---------------

void matmul_rvv_i8_2xVL(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M,
                        const unsigned long int N, const unsigned long int P) {
  // We work on 2 rows of the matrix at once
  const unsigned long int block_size = 2;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e8, m8, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    int8_t *b_ = (int8_t *)b + p;
    int8_t *c_ = c + p;

    asm volatile("vsetvli zero, %0, e8, m8, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      int8_t *a_ = (int8_t *)a + m * N;

      // Prefetch one row of matrix B
      int8_t *b__ = b_;
      asm volatile("vle8.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle8.v v24, (%0);" ::"r"(b__));
      b__ += P;

      int8_t *c__ = c_ + m * P;

      // Temporary variables
      int8_t t0, t1;

      // Original pointer
      int8_t *a__ = a_;

      // Keep rack of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1  = *a__;
      a__ = a_ + n++;

      // Only multiply on first iteration
      asm volatile("vmul.vx v0, v16, %0" ::"r"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vmul.vx v8, v16, %0" ::"r"(t1));
      t1 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle8.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v24" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v24" ::"r"(t1));
        t1 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle8.v v24, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v16" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v16" ::"r"(t1));
        t1 = *a__;
      }

      // Last iteration: store results
      asm volatile("vmacc.vx v0, %0, v24" ::"r"(t0));
      asm volatile("vse8.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v24" ::"r"(t1));
      asm volatile("vse8.v v8, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 4x4
// ---------------

void matmul_rvv_i8_4xVL(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M,
                        const unsigned long int N, const unsigned long int P) {
  // We work on 4 rows of the matrix at once
  const unsigned long int block_size = 4;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e8, m4, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    int8_t *b_ = (int8_t *)b + p;
    int8_t *c_ = c + p;

    asm volatile("vsetvli zero, %0, e8, m4, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      int8_t *a_ = (int8_t *)a + m * N;

      // Prefetch one row of matrix B
      int8_t *b__ = b_;
      asm volatile("vle8.v v16, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle8.v v20, (%0);" ::"r"(b__));
      b__ += P;

      int8_t *c__ = c_ + m * P;

      // Temporary variables
      int8_t t0, t1, t2, t3;

      // Original pointer
      int8_t *a__ = a_;

      // Keep track of number of iterations
      unsigned long int n = 1;

      // Prefetch one row of scalar values
      t0 = *a__, a__ += N;
      t1 = *a__, a__ += N;
      t2 = *a__, a__ += N;
      t3  = *a__;
      a__ = a_ + n++;

      // Only mutliply on first iteration
      asm volatile("vmul.vx v0, v16, %0" ::"r"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vmul.vx v4, v16, %0" ::"r"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vmul.vx v8, v16, %0" ::"r"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vmul.vx v12, v16, %0" ::"r"(t3));
      t3 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle8.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v20" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v20" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v20" ::"r"(t3));
        t3 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle8.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v16" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v16" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v16" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v16" ::"r"(t3));
        t3 = *a__;
      }

      // Last iteration: store results
      asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
      asm volatile("vse8.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v4, %0, v20" ::"r"(t1));
      asm volatile("vse8.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v20" ::"r"(t2));
      asm volatile("vse8.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v12, %0, v20" ::"r"(t3));
      asm volatile("vse8.v v12, (%0);" ::"r"(c__));
    }
  }
}

// ---------------
// 8x8
// ---------------

void matmul_rvv_i8_8xVL(int8_t *c, const int8_t *a, const int8_t *b, const unsigned long int M,
                        const unsigned long int N, const unsigned long int P) {
  // We work on 8 rows of the matrix at once
  const unsigned long int block_size = 8;
  unsigned long int       block_size_p;

  // Set the vector configuration
  asm volatile("vsetvli %0, %1, e8, m2, ta, ma" : "=r"(block_size_p) : "r"(P));

  // Slice the matrix into a manageable number of columns p_
  for (unsigned long int p = 0; p < P; p += block_size_p) {
    // Set the vector length
    const unsigned long int p_ = MIN(P - p, block_size_p);

    // Find pointers to the submatrices
    int8_t *b_ = (int8_t *)b + p;
    int8_t *c_ = c + p;

    asm volatile("vsetvli zero, %0, e8, m2, ta, ma" ::"r"(p_));

    // Iterate over the rows
    for (unsigned long int m = 0; m < M; m += block_size) {
      // Find pointer to the submatrices
      int8_t *a_ = (int8_t *)a + m * N;

      // Prefetch one row of matrix B
      int8_t *b__ = b_;
      asm volatile("vle8.v v18, (%0);" ::"r"(b__));
      b__ += P;
      asm volatile("vle8.v v20, (%0);" ::"r"(b__));
      b__ += P;

      int8_t *c__ = c_ + m * P;

      // Temporary variables
      int8_t t0, t1, t2, t3, t4, t5, t6, t7;

      // Original pointer
      int8_t *a__ = a_;

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
      asm volatile("vmul.vx v0, v18, %0" ::"r"(t0));
      t0 = *a__, a__ += N;
      asm volatile("vmul.vx v2, v18, %0" ::"r"(t1));
      t1 = *a__, a__ += N;
      asm volatile("vmul.vx v4, v18, %0" ::"r"(t2));
      t2 = *a__, a__ += N;
      asm volatile("vmul.vx v6, v18, %0" ::"r"(t3));
      t3 = *a__, a__ += N;
      asm volatile("vmul.vx v8, v18, %0" ::"r"(t4));
      t4 = *a__, a__ += N;
      asm volatile("vmul.vx v10, v18, %0" ::"r"(t5));
      t5 = *a__, a__ += N;
      asm volatile("vmul.vx v12, v18, %0" ::"r"(t6));
      t6 = *a__, a__ += N;
      asm volatile("vmul.vx v14, v18, %0" ::"r"(t7));
      t7 = *a__;

      while (n < N) {
        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle8.v v18, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v2, %0, v20" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v20" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v6, %0, v20" ::"r"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v20" ::"r"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vmacc.vx v10, %0, v20" ::"r"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v20" ::"r"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vmacc.vx v14, %0, v20" ::"r"(t7));
        t7 = *a__;

        // Calculate pointer to the matrix A
        a__ = a_ + n++;

        // Load one row of B
        asm volatile("vle8.v v20, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v18" ::"r"(t0));
        t0 = *a__, a__ += N;
        asm volatile("vmacc.vx v2, %0, v18" ::"r"(t1));
        t1 = *a__, a__ += N;
        asm volatile("vmacc.vx v4, %0, v18" ::"r"(t2));
        t2 = *a__, a__ += N;
        asm volatile("vmacc.vx v6, %0, v18" ::"r"(t3));
        t3 = *a__, a__ += N;
        asm volatile("vmacc.vx v8, %0, v18" ::"r"(t4));
        t4 = *a__, a__ += N;
        asm volatile("vmacc.vx v10, %0, v18" ::"r"(t5));
        t5 = *a__, a__ += N;
        asm volatile("vmacc.vx v12, %0, v18" ::"r"(t6));
        t6 = *a__, a__ += N;
        asm volatile("vmacc.vx v14, %0, v18" ::"r"(t7));
        t7 = *a__;
      }

      // Last iteration: store results
      asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
      asm volatile("vse8.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v2, %0, v20" ::"r"(t1));
      asm volatile("vse8.v v2, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v4, %0, v20" ::"r"(t2));
      asm volatile("vse8.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v6, %0, v20" ::"r"(t3));
      asm volatile("vse8.v v6, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v20" ::"r"(t4));
      asm volatile("vse8.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v10, %0, v20" ::"r"(t5));
      asm volatile("vse8.v v10, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v12, %0, v20" ::"r"(t6));
      asm volatile("vse8.v v12, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v14, %0, v20" ::"r"(t7));
      asm volatile("vse8.v v14, (%0);" ::"r"(c__));
    }
  }
}
