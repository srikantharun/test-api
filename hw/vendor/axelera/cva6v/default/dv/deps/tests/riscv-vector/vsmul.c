// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  uint64_t vxsat;
  VSET(3, e8, m1);
  VLOAD_8(v2, 127, 127, -50);
  VLOAD_8(v3, 127, 10, 127);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vsmul.vv v1, v2, v3");
  VCMP_I8(1, v1, 126, 9, -50);
  read_vxsat(vxsat);
  check_vxsat(1, vxsat, 0);
  reset_vxsat;
}

void TEST_CASE2() {
  uint64_t vxsat;
  VSET(3, e8, m1);
  VLOAD_8(v2, 127, 127, -50);
  VLOAD_8(v3, 127, 10, 127);
  VLOAD_8(v0, 5, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vsmul.vv v1, v2, v3, v0.t");
  VCMP_I8(2, v1, 126, 0, -50);
  read_vxsat(vxsat);
  check_vxsat(2, vxsat, 0);
  reset_vxsat;
}

void TEST_CASE3() {
  uint64_t vxsat;
  VSET(3, e8, m1);
  VLOAD_8(v2, 127, 63, -50);
  int8_t scalar = 55;
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vsmul.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_I8(3, v1, 54, 27, -22);
  read_vxsat(vxsat);
  check_vxsat(3, vxsat, 0);
  reset_vxsat;
}

void TEST_CASE4() {
  uint64_t vxsat;
  VSET(3, e8, m1);
  VLOAD_8(v2, 127, 127, -50);
  int8_t scalar = 55;
  VLOAD_8(v0, 5, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vsmul.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_I8(4, v1, 54, 0, -22);
  read_vxsat(vxsat);
  check_vxsat(4, vxsat, 0);
  reset_vxsat;
}

void TEST_CASE5() {
  uint64_t vxsat;
  VSET(3, e8, m1);
  VLOAD_8(v2, -128, -128, 127);
  VLOAD_8(v3, 127, -128, -128);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vsmul.vv v1, v2, v3");
  VCMP_I8(5, v1, -127, 127, -127);
  read_vxsat(vxsat);
  check_vxsat(5, vxsat, 1);
  reset_vxsat;
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  enable_fp();
  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());
  TEST_CASE5();
  EXIT_CHECK();
}
