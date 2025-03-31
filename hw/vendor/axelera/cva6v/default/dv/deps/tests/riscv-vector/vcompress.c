// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(4, e32, m1);
  VLOAD_32(v11, 12, 0, 0, 0);
  VSET(4, e32, m8);
  VLOAD_32(v8, 1, 2, 3, 4);
  VCLEAR(v0);
  __asm__ volatile("vcompress.vm v0, v8, v11");
  VCMP_U32(1, v0, 3, 4, 0, 0);
}

void TEST_CASE2() {
  VSET(4, e32, m1);
  VLOAD_32(v2, 0xAAAA, 0x5555, 0xAAAA, 0x5555);
  VLOAD_32(v4, 1, 2, 3, 4);
  VLOAD_32(v0, 0xC, 0, 0, 0);
  __asm__ volatile("vcompress.vm v2, v4, v0");
  VCMP_U32(2, v2, 3, 4, 0xAAAA, 0x5555);
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  enable_fp();
  TEST_CASE1();
  TEST_CASE2();
  EXIT_CHECK();
}
