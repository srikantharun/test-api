// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

// Test all the different output possibilities
void TEST_CASE1(void) {
  CLEAR_FFLAGS;
  CHECK_FFLAGS(0);

  VSET(16, e16, m1);
  VLOAD_16(v2, mInfh, pInfh, qNaNh, sNaNh, 0x3b27, 0xc767, pZero, mZeroh, 0x8075, 0x00c5, mInfh, pInfh, qNaNh, sNaNh,
           0x3b27, 0xb767);
  asm volatile("vfclass.v v1, v2");
  VCMP_U16(1, v1, CLASS_mInf, CLASS_pInf, CLASS_qNAN, CLASS_sNAN, CLASS_pNorm, CLASS_mNorm, CLASS_pZero, CLASS_mZero,
           CLASS_mSub, CLASS_pSub, CLASS_mInf, CLASS_pInf, CLASS_qNAN, CLASS_sNAN, CLASS_pNorm, CLASS_mNorm);

  VSET(16, e32, m2);
  VLOAD_32(v4, mInff, pInff, qNaNf, sNaNf, 0x3f738772, 0xbdef32e4, pZero, mZerof, 0x80000075, 0x000000c5, mInff, pInff,
           qNaNf, sNaNf, 0x3f738772, 0xbdef32e4);
  asm volatile("vfclass.v v2, v4");
  VCMP_U32(2, v2, CLASS_mInf, CLASS_pInf, CLASS_qNAN, CLASS_sNAN, CLASS_pNorm, CLASS_mNorm, CLASS_pZero, CLASS_mZero,
           CLASS_mSub, CLASS_pSub, CLASS_mInf, CLASS_pInf, CLASS_qNAN, CLASS_sNAN, CLASS_pNorm, CLASS_mNorm);
};

// Test all the different output possibilities
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  VLOAD_16(v2, mInfh, pInfh, qNaNh, sNaNh, 0x3b27, 0xc767, pZero, mZeroh, 0x8075, 0x00c5, mInfh, pInfh, qNaNh, sNaNh,
           0x3b27, 0xb767);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vfclass.v v1, v2, v0.t");
  VCMP_U16(4, v1, 0, CLASS_pInf, 0, CLASS_sNAN, 0, CLASS_mNorm, 0, CLASS_mZero, 0, CLASS_pSub, 0, CLASS_pInf, 0,
           CLASS_sNAN, 0, CLASS_mNorm);

  VSET(16, e32, m2);
  VLOAD_32(v4, mInff, pInff, qNaNf, sNaNf, 0x3f738772, 0xbdef32e4, pZero, mZerof, 0x80000075, 0x000000c5, mInff, pInff,
           qNaNf, sNaNf, 0x3f738772, 0xbdef32e4);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v2);
  asm volatile("vfclass.v v2, v4, v0.t");
  VCMP_U32(5, v2, 0, CLASS_pInf, 0, CLASS_sNAN, 0, CLASS_mNorm, 0, CLASS_mZero, 0, CLASS_pSub, 0, CLASS_pInf, 0,
           CLASS_sNAN, 0, CLASS_mNorm);
  CHECK_FFLAGS(0);
};

int main(void) {
  enable_vec();
  enable_fp();

  // No exception should be raised by vfclass.v
  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());

  EXIT_CHECK();
}
