// Author: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#include "float_macros.h"
#include "vector_macros.h"

void TEST_CASE0(void) {
  VSET(2, e32, m1);
  VLOAD_32(v4, 0x00718abc, 0x7f765432);
  asm volatile("vfrsqrt7.v v2, v4");
  VCMP_U32(0, v2, 0x5f080000, 0x1f820000);
};

void TEST_CASE1(void) {
  VSET(16, e16, m1);
  VLOAD_16(v2, mInfh, pInfh, qNaNh, sNaNh, pZero, mZeroh, 0xba72, 0x3a12, 0x3af7, 0x00fe, 0x01e6, 0x75e6, 0x80fe,
           0xb5fd, 0xb4e7, 0x7bc0);
  asm volatile("vfrsqrt7.v v1, v2");
  VCMP_U16(1, v1, qNaNh, pZero, qNaNh, qNaNh, pInfh, mInfh, 0x7e00, 0x3c98, 0x3c48, 0x5c00, 0x59d0, 0x1e98, qNaNh,
           qNaNh, qNaNh, 0x1c10);

  VSET(16, e32, m2);
  VLOAD_32(v4, mInff, pInff, qNaNf, sNaNf, pZero, mZerof, 0xfe7fca13, 0x00800000, 0x807ee93e, 0x803ee93e, 0x00200000,
           0x00400000, 0x00800000, 0xff787a12, 0xff000005, 0x800dd27e);
  asm volatile("vfrsqrt7.v v2, v4");
  VCMP_U32(2, v2, qNaNf, pZero, qNaNf, qNaNf, pInff, mInff, qNaNf, 0x5eff0000, qNaNf, qNaNf, 0x5f7f0000, 0x5f340000,
           0x5eff0000, qNaNf, qNaNf, qNaNf);
};

// Test to check DZ flag
void TEST_CASE2(void) {
  CLEAR_FFLAGS;
  VSET(16, e16, m1);
  CHECK_FFLAGS(0);
  VLOAD_16(v2, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh,
           pZero, mZeroh);
  asm volatile("vfrsqrt7.v v1, v2");
  VCMP_U16(4, v1, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh,
           pInfh, mInfh);
  CHECK_FFLAGS(DZ);

  CLEAR_FFLAGS;
  VSET(16, e32, m2);
  CHECK_FFLAGS(0);
  VLOAD_32(v4, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof,
           pZero, mZerof);
  asm volatile("vfrsqrt7.v v2, v4");
  VCMP_U32(5, v2, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff,
           pInff, mInff);
  CHECK_FFLAGS(DZ);
};

// Test to check NV flag
void TEST_CASE3(void) {
  CLEAR_FFLAGS;
  VSET(16, e16, m1);
  CHECK_FFLAGS(0);
  VLOAD_16(v2, mInfh, sNaNh, mInfh, 0x801e, 0x800e, mInfh, mInfh, 0x8030, sNaNh, mInfh, sNaNh, sNaNh, mInfh, sNaNh,
           sNaNh, mInfh);
  asm volatile("vfrsqrt7.v v1, v2");
  VCMP_U16(7, v1, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh, qNaNh,
           qNaNh, qNaNh);
  CHECK_FFLAGS(NV);

  CLEAR_FFLAGS;
  VSET(16, e32, m2);
  CHECK_FFLAGS(0);
  VLOAD_32(v4, 0x800dd27e, mInff, 0x8005d27c, mInff, sNaNf, 0x8000527c, mInff, 0x8000107c, sNaNf, mInff, sNaNf, mInff,
           0x8000d27c, sNaNf, sNaNf, mInff);
  asm volatile("vfrsqrt7.v v2, v4");
  VCMP_U32(8, v2, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf, qNaNf,
           qNaNf, qNaNf);
  CHECK_FFLAGS(NV);
};

int main(void) {
  enable_vec();
  enable_fp();

  TEST_CASE0();
  TEST_CASE1();
  TEST_CASE2();
  TEST_CASE3();

  EXIT_CHECK();
}
