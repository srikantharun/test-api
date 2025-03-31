// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(16, e8, m1);
  VCLEAR(v2);
  __asm__ volatile("vid.v v2");
  VCMP_U8(1, v2, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);

  VSET(16, e16, m1);
  VCLEAR(v2);
  __asm__ volatile("vid.v v2");
  VCMP_U16(2, v2, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);

  VSET(16, e32, m2);
  VCLEAR(v2);
  __asm__ volatile("vid.v v2");
  VCMP_U32(3, v2, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
}

void TEST_CASE2() {
  VSET(16, e8, m1);
  VLOAD_8(v0, 0x55, 0xAA, 0, 0, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vid.v v2, v0.t");
  VCMP_U8(4, v2, 0, 0, 2, 0, 4, 0, 6, 0, 0, 9, 0, 11, 0, 13, 0, 15);

  VSET(16, e16, m1);
  VLOAD_8(v0, 0x55, 0xAA, 0, 0, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vid.v v2, v0.t");
  VCMP_U16(5, v2, 0, 0, 2, 0, 4, 0, 6, 0, 0, 9, 0, 11, 0, 13, 0, 15);

  VSET(16, e32, m2);
  VLOAD_8(v0, 0x55, 0xAA, 0, 0, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vid.v v2, v0.t");
  VCMP_U32(6, v2, 0, 0, 2, 0, 4, 0, 6, 0, 0, 9, 0, 11, 0, 13, 0, 15);
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  enable_fp();

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());

  EXIT_CHECK();
}
