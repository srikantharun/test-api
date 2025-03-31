// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>
//         Matteo Perotti <mperotti@student.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

void TEST_CASE1(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                            -0.9380
  BOX_HALF_IN_FLOAT(fscalar_16, 0xbb81);
  VCLEAR(v1);
  asm volatile("vfmv.v.f v1, %[A]" ::[A] "f"(fscalar_16));
  //              -0.9380, -0.9380, -0.9380, -0.9380, -0.9380, -0.9380, -0.9380,
  //              -0.9380, -0.9380, -0.9380, -0.9380, -0.9380, -0.9380, -0.9380,
  //              -0.9380, -0.9380
  VCMP_U16(1, v1, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0xbb81,
           0xbb81, 0xbb81, 0xbb81, 0xbb81);

  VSET(16, e32, m2);
  float fscalar_32;
  //                             -0.96056187
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0xbf75e762);
  VCLEAR(v2);
  asm volatile("vfmv.v.f v2, %[A]" ::[A] "f"(fscalar_32));
  //               -0.96056187, -0.96056187, -0.96056187, -0.96056187,
  //               -0.96056187, -0.96056187, -0.96056187, -0.96056187,
  //               -0.96056187, -0.96056187, -0.96056187, -0.96056187,
  //               -0.96056187, -0.96056187, -0.96056187, -0.96056187
  VCMP_U32(2, v2, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762,
           0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762);
};

int main(void) {
  enable_vec();
  enable_fp();

  TEST_CASE1();

  EXIT_CHECK();
}
