#include "../../env/rag_generated_vector_init.h"

main:
                  # Set up a valid vector configuration (SEW=32, LMUL=1)
                  vsetvli t0, zero, e32, m1

                  # Initialize v1 with some values
                  vid.v v1             # v1 = [0, 1, 2, 3, ...] (vector index)

                  # Case 1: Use an uninitialized mask register (v0)
                  # This might cause unpredictable behavior at runtime
                  vcompress.vm v2, v1, v0  # ERROR: v0 is not initialized

                  # Case 2: Use an invalid LMUL setting
                  vsetvli t0, zero, e32, mf8   # Extremely small LMUL
                  vcompress.vm v3, v1, v0  # Might be illegal due to LMUL constraints

                  # Case 3: VL too large (potentially illegal if VL > VLMAX)
                  li t0, 1000
                  csrw vl, t0
                  vcompress.vm v4, v1, v0  # VL setting might cause illegal instruction

main_2:
                  # Set up a valid vector configuration (SEW=32, LMUL=1)
                  vsetvli t0, zero, e32, m1
                  vid.v v1             # v1 = [0, 1, 2, 3, ...] (vector index)

                  ##### CASE 1: ILLEGAL MASK VALUE (v0 = all 0) #####
                  vmv.v.i v0, 0        # Mask is all 0 → `vcompress.vm` should do nothing
                  vcompress.vm v2, v1, v0  # Might cause an issue if v0 is required to have at least one set bit

                  ##### CASE 2: ILLEGAL LMUL SETTINGS #####
                  vsetvli t0, zero, e32, m2  # LMUL=2
                  vcompress.vm v3, v1, v0    # Might be illegal if VL is odd

                  ##### CASE 3: OVERLAPPING SOURCE AND DESTINATION #####
                  vsetvli t0, zero, e32, m1
                  vcompress.vm v1, v1, v0    # Illegal? Overwriting source while compressing

                  ##### CASE 4: INVALID SEW SETTING #####
                  vsetvli t0, zero, e8, m1  # SEW=8 (some implementations don't support)
                  vcompress.vm v4, v1, v0   # Illegal if SEW=8 is not supported

#include "../../env/rag_generated_vector_end.h"
