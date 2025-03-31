// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matteo Perotti <mperotti@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>
//         Shafiullah Khan <shafi.ullah@10xengineers.ai>

#include "float_macros.h"
#include "vector_macros.h"

void TEST_CASE0(void) {
  VSET(2, e32, m1);
  VLOAD_32(v4, 0x00718abc, 0x7f765432);
  asm volatile("vfrec7.v v2, v4");
  VCMP_U32(0, v2, 0x7e900000, 0x00214000);
};

void TEST_CASE1(void) {
  VSET(16, e16, m1);
  VLOAD_16(v2, mInfh, pInfh, qNaNh, sNaNh, pZero, mZeroh, 0xba72, 0x3a12, 0x3af7, 0x00fe, 0x01e6, 0x75e6, 0x80fe,
           0xb5fd, 0xb4e7, 0x7bc0);
  asm volatile("vfrec7.v v1, v2");
  VCMP_U16(1, v1, mZeroh, pZero, qNaNh, qNaNh, pInfh, mInfh, 0xbcf8, 0x3d40, 0x3c98, pInfh, 0x7838, 0x02b8, mInfh,
           0xc158, 0xc288, 0x0108);

  VSET(16, e32, m2);
  VLOAD_32(v4, mInff, pInff, qNaNf, sNaNf, pZero, mZerof, 0xfe7fca13, 0x00800000, 0x807ee93e, 0x803ee93e, 0x00200000,
           0x00400000, 0x00800000, 0xff787a12, 0xff000005, 0x800dd27e);
  asm volatile("vfrec7.v v2, v4");
  VCMP_U32(2, v2, mZerof, pZero, qNaNf, qNaNf, pInff, mInff, 0x80800000, 0x7e7f0000, 0xfe810000, 0xff020000, 0x7f7f0000,
           0x7eff0000, 0x7e7f0000, 0x80210000, 0x803fc000, mInff);
};

// Test to check DZ flag
void TEST_CASE2(void) {
  CLEAR_FFLAGS;
  VSET(16, e16, m1);
  CHECK_FFLAGS(0);
  VLOAD_16(v2, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh, pZero, mZeroh,
           pZero, mZeroh);
  asm volatile("vfrec7.v v1, v2");
  VCMP_U16(4, v1, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh, pInfh, mInfh,
           pInfh, mInfh);
  CHECK_FFLAGS(DZ);

  CLEAR_FFLAGS;
  VSET(16, e32, m2);
  CHECK_FFLAGS(0);
  VLOAD_32(v4, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof, pZero, mZerof,
           pZero, mZerof);
  asm volatile("vfrec7.v v2, v4");
  VCMP_U32(5, v2, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff, pInff, mInff,
           pInff, mInff);
  CHECK_FFLAGS(DZ);
};

// Test to check NX,OF flags as well as for subnormal numbers with sig=00..
void TEST_CASE3(void) {
  CLEAR_FFLAGS;
  VSET(16, e16, m1);
  CHECK_FFLAGS(0);
  CHANGE_RM(RM_RUP);
  VLOAD_16(v2, 0x80fe, 0x807e, 0x803e, 0x801e, 0x800e, 0x8006, 0x8002, 0x8030, 0x00fe, 0x007e, 0x003e, 0x001e, 0x000e,
           0x0006, 0x0002, 0x0030);
  asm volatile("vfrec7.v v1, v2");
  VCMP_U16(7, v1, mMaxh, mMaxh, mMaxh, mMaxh, mMaxh, mMaxh, mMaxh, mMaxh, pInfh, pInfh, pInfh, pInfh, pInfh, pInfh,
           pInfh, pInfh);
  CHECK_FFLAGS(NX | OF);

  CLEAR_FFLAGS;
  VSET(16, e32, m2);
  CHECK_FFLAGS(0);
  CHANGE_RM(RM_RDN);
  VLOAD_32(v4, 0x800dd27e, 0x8005d27e, 0x8005d27c, 0x8001d27c, 0x8000d27c, 0x8000527c, 0x8000127c, 0x8000107c,
           0x000dd27e, 0x0005d27e, 0x0005d27c, 0x0001d27c, 0x0000d27c, 0x0000527c, 0x0000127c, 0x0000107c);
  asm volatile("vfrec7.v v2, v4");
  VCMP_U32(8, v2, mInff, mInff, mInff, mInff, mInff, mInff, mInff, mInff, pMaxf, pMaxf, pMaxf, pMaxf, pMaxf, pMaxf,
           pMaxf, pMaxf);
  CHECK_FFLAGS(NX | OF);
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
