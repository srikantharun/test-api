// Description: Generalized matrix multiplication kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#include <gemm.h>

// A is an m x n matrix, B is an n x p matrix, and C is an m x p matrix, as used
// in the example on
// https://en.wikipedia.org/wiki/Matrix_multiplication#Definition
void gemm_i32_rvv(unsigned long m, unsigned long n, unsigned long p,
                  const int32_t *A,  // m * n matrix
                  const int32_t *B,  // n * p matrix
                  int32_t       *C   // m * p matrix
) {
  // note: m must be a multiple of 16
  for (unsigned long lm = 0; lm < m; lm += 16) {
    int32_t *C_addr = C;

    unsigned long vl;
    for (unsigned long lp = 0; lp < p; lp += vl) {
      asm volatile("vsetvli     %0, %1, e32, m1, ta, ma;" : "=r"(vl) : "r"(p - lp));

      int32_t *C_addr_ld = C_addr;
      asm volatile("vle32.v     v0,  (%0);" ::"r"(C_addr_ld));
      asm volatile("vle32.v     v1,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v2,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v3,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v4,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v5,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v6,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v7,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v8,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v9,  (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v10, (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v11, (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v12, (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v13, (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v14, (%0);" ::"r"(C_addr_ld += p));
      asm volatile("vle32.v     v15, (%0);" ::"r"(C_addr_ld += p));

      const int32_t *A_addr = A;
      const int32_t *B_addr = B + lp;
      asm volatile("vle32.v     v16, (%0);" ::"r"(B_addr));

      for (unsigned long ln = 0; ln < n; ln += 2) {
        asm volatile("vle32.v     v17, (%0);" ::"r"(B_addr += p));

        const int32_t *A_addr_1 = A_addr++;
        asm volatile("vmacc.vx    v0,  %0, v16;" ::"r"(*(A_addr_1)));
        asm volatile("vmacc.vx    v1,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v2,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v3,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v4,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v5,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v6,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v7,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v8,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v9,  %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v10, %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v11, %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v12, %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v13, %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v14, %0, v16;" ::"r"(*(A_addr_1 += n)));
        asm volatile("vmacc.vx    v15, %0, v16;" ::"r"(*(A_addr_1 += n)));

        asm volatile("vle32.v     v16, (%0);" ::"r"(B_addr += p));

        const int32_t *A_addr_2 = A_addr++;
        asm volatile("vmacc.vx    v0,  %0, v17;" ::"r"(*(A_addr_2)));
        asm volatile("vmacc.vx    v1,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v2,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v3,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v4,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v5,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v6,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v7,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v8,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v9,  %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v10, %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v11, %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v12, %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v13, %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v14, %0, v17;" ::"r"(*(A_addr_2 += n)));
        asm volatile("vmacc.vx    v15, %0, v17;" ::"r"(*(A_addr_2 += n)));
      }

      int32_t *C_addr_st = C_addr;
      asm volatile("vse32.v     v0,  (%0);" ::"r"(C_addr_st));
      asm volatile("vse32.v     v1,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v2,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v3,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v4,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v5,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v6,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v7,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v8,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v9,  (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v10, (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v11, (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v12, (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v13, (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v14, (%0);" ::"r"(C_addr_st += p));
      asm volatile("vse32.v     v15, (%0);" ::"r"(C_addr_st += p));

      C_addr += vl;
    }

    A += n << 4;  // 16 * n;
    C += p << 4;  // 16 * p;
  }
}
