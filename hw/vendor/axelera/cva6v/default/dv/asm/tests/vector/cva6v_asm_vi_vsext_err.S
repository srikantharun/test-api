#include "../../env/rag_generated_vector_init.h"

CASE_1_INVALID_LMUL_FOR_SEW:
                  vsetvli t0, zero, e8, m1    # Set SEW=32, LMUL=1
                  vsext.vf8 v1, v2, v0.t       # Valid extension with SEW=32
                  vsext.vf4 v3, v4, v0.t       # Invalid extension if SEW is too small for vsext.vf4
                  vsext.vf2 v5, v6, v0.t       # Invalid extension if SEW is too small for vsext.vf2

CASE_2_OVERLAPPING_SOURCE_AND_DESTINATION:
                  vsetvli t0, zero, e32, m1    # Set SEW=32, LMUL=1
                  vsext.vf8 v7, v7, v0.t       # Overwrite source with destination (undefined behavior)
                  vsext.vf4 v8, v8, v0.t       # Overwrite source with destination (undefined behavior)
                  vsetvli t0, zero, e16, m1    # Set SEW=16, LMUL=1
                  vsext.vf2 v9, v9, v0.t       # Overwrite source with destination (undefined behavior)

CASE_3_INVALID_VECTOR_LENGTH:
                  li t0, 512                   # VL exceeds VLMAX (invalid VL)
                  vsetvli t0, t0, e32           # Ensure correct vsetvli configuration
                  vsext.vf8 v10, v11, v0.t     # Expect error: VL exceeds VLMAX
                  vsext.vf4 v12, v13, v0.t     # Expect error: VL exceeds VLMAX
                  vsext.vf2 v14, v15, v0.t     # Expect error: VL exceeds VLMAX

CASE_4_VECTOR_MASK_ZERO:
                  vsetvli t0, zero, e32, m1    # Set SEW=32, LMUL=1
                  vmv.v.i v16, 0               # Mask is all 0
                  vsext.vf8 v17, v18, v0.t     # No extension happens due to mask
                  vsext.vf4 v19, v20, v0.t     # No extension happens due to mask
                  vsetvli t0, zero, e16, m1    # Set SEW=16, LMUL=1
                  vsext.vf2 v21, v22, v0.t     # No extension happens due to mask

CASE_5_UNSUPPORTED_VECTOR_EXTENSION:
                  vsetvli t0, zero, e32, m1   # Unsupported SEW for vsext.vf8
                  vsext.vf8 v23, v24, v0.t     # Expect error: Unsupported SEW
                  vsext.vf4 v25, v26, v0.t     # Expect error: Unsupported SEW
                  vsetvli t0, zero, e16, m1    # Set SEW=16, LMUL=1
                  vsext.vf2 v27, v28, v0.t     # Expect error: Unsupported SEW

CASE_6_INCORRECT_VECTOR_LENGTH_ALIGNMENT:
                  li t1, 11                    # VL is odd
                  vsetvli t0, t1, e32           # Invalid VL setting
                  vsext.vf8 v29, v30, v0.t     # Expect misalignment error
                  vsext.vf4 v31, v0, v0.t      # Expect misalignment error
                  vsext.vf2 v1, v2, v0.t       # Expect misalignment error

CASE_7_ZERO_VECTOR_ADDITION:
                  vsetvli t0, zero, e32, m1    # Set SEW=32, LMUL=1
                  vmv.v.i v3, 0               # Set v3 to all zeros
                  vsext.vf8 v4, v5, v0.t      # Expect v4 = v5 (no change)
                  vsext.vf4 v6, v7, v0.t      # Expect v6 = v7 (no change)
                  vsetvli t0, zero, e16, m1    # Set SEW=16, LMUL=1
                  vsext.vf2 v8, v9, v0.t      # Expect v8 = v9 (no change)

CASE_8_VECTOR_MASK_WITH_ALTERNATE_BITS:
                  vsetvli t0, zero, e32, m1    # Set SEW=32, LMUL=1
                  li t2, 0xAAAA               # Mask pattern: alternate bits
                  vmv.v.x v0, t2              # Set the mask
                  vsext.vf8 v10, v11, v0.t     # Partial extension due to mask
                  vsext.vf4 v12, v13, v0.t     # Partial extension due to mask
                  vsext.vf2 v14, v15, v0.t     # Partial extension due to mask

CASE_9_OVERFLOW_CARRY:
                  vsetvli t0, zero, e32, m1    # Set SEW=32, LMUL=1
                  li t3, 0xFFFFFFFF            # Max unsigned 32-bit value
                  vmv.v.x v16, t3              # Load max value
                  vsext.vf8 v17, v18, v0.t     # Expect overflow carry
                  vsext.vf4 v19, v20, v0.t     # Expect overflow carry
                  vsetvli t0, zero, e16, m1    # Set SEW=16, LMUL=1
                  vsext.vf2 v21, v22, v0.t     # Expect overflow carry

CASE_10_UNALIGNED_VECTOR_STORE:
                  vsetvli t0, zero, e32, m1    # Set SEW=32, LMUL=1
                  li t4, 9                    # VL = odd, causing misalignment
                  vsetvli t0, t4, e8
                  vsext.vf8 v23, v24, v0.t     # Expect misaligned vector store
                  vsext.vf4 v25, v26, v0.t     # Expect misaligned vector store
                  vsetvli t0, zero, e16, m1    # Set SEW=16, LMUL=1
                  vsext.vf2 v27, v28, v0.t     # Expect misaligned vector store

CASE_11_VALID_VSEXT:
                  vsetvli t0, zero, e32, m1     # Set SEW=32, LMUL=1 (valid for vsext.vf8)
                  vsext.vf8 v29, v30, v0.t      # Valid vsext.vf8 with SEW=32

                  vsetvli t0, zero, e16, m1     # Set SEW=16, LMUL=1 (valid for vsext.vf2)
                  vsext.vf2 v31, v2, v0.t       # Valid vsext.vf2 with SEW=16

                  vsetvli t0, zero, e32, m1     # Set SEW=32, LMUL=1 (valid for vsext.vf4)
                  vsext.vf4 v3, v4, v0.t        # Valid vsext.vf4 with SEW=32

#include "../../env/rag_generated_vector_end.h"
