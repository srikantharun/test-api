// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(16, e8, m1);
  VLOAD_8(v3, 8, 0, 0, 0, 0, 0, 0, 0);
  __asm__ volatile("vmsbf.m v2, v3");
  VCMP_U8(1, v2, 7, 0, 0, 0, 0, 0, 0, 0);
}

void TEST_CASE2() {
  VSET(16, e8, m1);
  VLOAD_8(v3, 8, 0, 0, 0, 0, 0, 0, 0);
  VLOAD_8(v0, 3, 0, 0, 0, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vmset.m v2");
  __asm__ volatile("vmsbf.m v2, v3, v0.t");
  VCMP_U8(2, v2, 0xff, 0xff, 0, 0, 0, 0, 0, 0);
}

// VS2 and VD do not need to be LMUL aligned
void TEST_CASE3() {
  VSET(16, e8, m1);
  VLOAD_8(v3, 8, 0, 0, 0, 0, 0, 0, 0);
  VSET(16, e8, m4);
  __asm__ volatile("vmsbf.m v2, v3");
  VSET(16, e8, m1);
  VCMP_U8(3, v2, 7, 0, 0, 0, 0, 0, 0, 0);
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
