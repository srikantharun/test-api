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
  //              -0.1481, -0.1797, -0.5454,  0.3228,  0.3237, -0.7212, -0.5195,
  //              -0.4500,  0.2681,  0.7300,  0.5059,  0.5830,  0.3198, -0.1713,
  //              -0.6431,  0.4841
  VLOAD_16(v2, 0xb0bd, 0xb1c0, 0xb85d, 0x352a, 0x352e, 0xb9c5, 0xb828, 0xb733, 0x344a, 0x39d7, 0x380c, 0x38aa, 0x351e,
           0xb17b, 0xb925, 0x37bf);
  float fscalar_16;
  //                            -0.9380
  BOX_HALF_IN_FLOAT(fscalar_16, 0xbb81);
  VLOAD_8(v0, 0x0F, 0xAA);
  asm volatile("vfmerge.vfm v1, v2, %[A], v0" ::[A] "f"(fscalar_16));
  //               -0.9380, -0.9380, -0.9380, -0.9380,  0.3237, -0.7212,
  //               -0.5195, -0.4500,  0.2681, -0.9380,  0.5059, -0.9380, 0.3198,
  //               -0.9380, -0.6431, -0.9380
  VCMP_U16(1, v1, 0xbb81, 0xbb81, 0xbb81, 0xbb81, 0x352e, 0xb9c5, 0xb828, 0xb733, 0x344a, 0xbb81, 0x380c, 0xbb81,
           0x351e, 0xbb81, 0xb925, 0xbb81);

  VSET(16, e32, m2);
  //               0.86539453, -0.53925377, -0.47128764,  0.99265540,
  //               0.32128176, -0.47335613, -0.30028856,  0.44394016,
  //               -0.72540921, -0.26464799,  0.77351445, -0.21725702,
  //               -0.25191557, -0.53123665,  0.80404943,  0.81841671
  VLOAD_32(v4, 0x3f5d8a7f, 0xbf0a0c89, 0xbef14c9d, 0x3f7e1eaa, 0x3ea47f0b, 0xbef25bbc, 0xbe99bf6c, 0x3ee34c20,
           0xbf39b46b, 0xbe877ff1, 0x3f46050b, 0xbe5e78a0, 0xbe80fb14, 0xbf07ff20, 0x3f4dd62f, 0x3f5183c2);
  float fscalar_32;
  //                             -0.96056187
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0xbf75e762);
  VLOAD_8(v0, 0x0F, 0xAA);
  asm volatile("vfmerge.vfm v2, v4, %[A], v0" ::[A] "f"(fscalar_32));
  //               -0.96056187, -0.96056187, -0.96056187, -0.96056187,
  //               0.32128176, -0.47335613, -0.30028856,  0.44394016,
  //               -0.72540921, -0.96056187,  0.77351445, -0.96056187,
  //               -0.25191557, -0.96056187,  0.80404943, -0.96056187
  VCMP_U32(2, v2, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0xbf75e762, 0x3ea47f0b, 0xbef25bbc, 0xbe99bf6c, 0x3ee34c20,
           0xbf39b46b, 0xbf75e762, 0x3f46050b, 0xbf75e762, 0xbe80fb14, 0xbf75e762, 0x3f4dd62f, 0xbf75e762);
};

int main(void) {
  enable_vec();
  enable_fp();

  TEST_CASE1();

  EXIT_CHECK();
}
