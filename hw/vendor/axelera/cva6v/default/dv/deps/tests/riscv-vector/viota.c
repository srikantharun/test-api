// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(2, e8, m1);
  VLOAD_8(v1, 0b10001001, 0);
  VSET(16, e8, m1);
  asm volatile("viota.m v2, v1");
  VCMP_U8(1, v2, 0, 1, 1, 1, 2, 2, 2, 2);
}

void TEST_CASE2() {
  VSET(16, e8, m1);
  VCLEAR(v2);
  VLOAD_8(v2, 0, 1, 2, 3, 4, 5, 6, 7);
  VSET(2, e8, m1);
  VLOAD_8(v1, 0b10001001, 0);
  VLOAD_8(v0, 0b11000111, 0);
  VSET(16, e8, m1);
  asm volatile("viota.m v2, v1, v0.t");
  VCMP_U8(2, v2, 0, 1, 1, 3, 4, 5, 1, 1);
}

// VS2 does not need to be LMUL aligned
void TEST_CASE3() {
  VSET(2, e8, m1);
  VLOAD_8(v1, 0b10001001, 0);
  VSET(16, e8, m2);
  asm volatile("viota.m v2, v1");
  VCMP_U8(3, v2, 0, 1, 1, 1, 2, 2, 2, 2);
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  enable_fp();
  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  EXIT_CHECK();
}
