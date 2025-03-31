// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  VLOAD_8(v6, 1, 0, 4, 3, 2);
  __asm__ volatile("vrgather.vv v2, v4, v6");
  VCMP_U8(1, v2, 20, 10, 50, 40, 30);
}

void TEST_CASE2() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  VLOAD_8(v6, 1, 0, 4, 3, 2);
  VLOAD_8(v0, 26, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vrgather.vv v2, v4, v6, v0.t");
  VCMP_U8(2, v2, 0, 10, 0, 40, 30);
}

void TEST_CASE3() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  uint64_t scalar = 3;
  __asm__ volatile("vrgather.vx v2, v4, %[A]" ::[A] "r"(scalar));
  VCMP_U8(3, v2, 40, 40, 40, 40, 40);
}

void TEST_CASE4() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  uint64_t scalar = 3;
  VLOAD_8(v0, 7, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vrgather.vx v2, v4, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U8(4, v2, 40, 40, 40, 0, 0);
}

void TEST_CASE5() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  __asm__ volatile("vrgather.vi v2, v4, 3");
  VCMP_U8(5, v2, 40, 40, 40, 40, 40);
}

void TEST_CASE6() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  VLOAD_8(v0, 7, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vrgather.vi v2, v4, 3, v0.t");
  VCMP_U8(6, v2, 40, 40, 40, 0, 0);
}

void TEST_CASE7() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  VLOAD_16(v6, 1, 0, 4, 3, 2);
  __asm__ volatile("vrgatherei16.vv v2, v4, v6");
  VCMP_U8(7, v2, 20, 10, 50, 40, 30);
}

void TEST_CASE8() {
  VSET(5, e8, m1);
  VLOAD_8(v4, 10, 20, 30, 40, 50);
  VLOAD_16(v6, 1, 0, 4, 3, 2);
  VLOAD_8(v0, 26, 0, 0, 0, 0);
  VCLEAR(v2);
  __asm__ volatile("vrgatherei16.vv v2, v4, v6, v0.t");
  VCMP_U8(8, v2, 0, 10, 0, 40, 30);
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());
  TEST_CASE5();
  MASKED_TEST(TEST_CASE6());
  TEST_CASE7();
  MASKED_TEST(TEST_CASE8());
  EXIT_CHECK();
}
