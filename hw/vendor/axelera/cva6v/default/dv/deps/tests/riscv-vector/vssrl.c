// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0xff, 0x00, 0xf0, 0x0f);
  VLOAD_8(v3, 1, 2, 3, 4);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vssrl.vv v1, v2, v3");
  VCMP_U8(1, v1, 0x7f, 0, 0x1e, 0x00);
}

void TEST_CASE2() {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0xff, 0x00, 0xf0, 0x0f);
  VLOAD_8(v3, 1, 2, 3, 4);
  VLOAD_8(v0, 5, 0, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vssrl.vv v1, v2, v3, v0.t");
  VCMP_U8(2, v1, 0x7f, 0, 0x1e, 0);
}

void TEST_CASE3() {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0xff, 0x00, 0xf0, 0x0f);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vssrl.vi v1, v2, 5");
  VCMP_U8(3, v1, 7, 0, 7, 0);
}

void TEST_CASE4() {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0xff, 0x00, 0xf0, 0x0f);
  VLOAD_8(v0, 5, 0, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vssrl.vi v1, v2, 5, v0.t");
  VCMP_U8(4, v1, 7, 0, 7, 0);
}

void TEST_CASE5() {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0xff, 0x00, 0xf0, 0x0f);
  uint64_t scalar = 5;
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vssrl.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U8(5, v1, 7, 0, 7, 0);
}

void TEST_CASE6() {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0xff, 0x00, 0xf0, 0x0f);
  uint64_t scalar = 5;
  VLOAD_8(v0, 5, 0, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vssrl.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U8(6, v1, 7, 0, 7, 0);
}

void TEST_CASE7() {
  VSET(8, e8, m1);
  VLOAD_8(v2, 0xb, 0xb, 0xb, 0xb, 0xa, 0xa, 0xc, 0xc);
  VLOAD_8(v3, 1, 2, 3, 4, 2, 3, 2, 3);
  __asm__ volatile("csrw vxrm, 1");
  __asm__ volatile("vssrl.vv v1, v2, v3");
  VCMP_U8(7, v1, 0x6, 0x3, 0x1, 0x1, 0x2, 0x1, 0x3, 0x2);
}

void TEST_CASE8() {
  VSET(8, e8, m1);
  VLOAD_8(v2, 0xb, 0xb, 0xb, 0xb, 0xa, 0xa, 0xc, 0xc);
  VLOAD_8(v3, 1, 2, 3, 4, 2, 3, 2, 3);
  __asm__ volatile("csrw vxrm, 3");
  __asm__ volatile("vssrl.vv v1, v2, v3");
  VCMP_U8(8, v1, 0x5, 0x3, 0x1, 0x1, 0x3, 0x1, 0x3, 0x1);
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
  MASKED_TEST(TEST_CASE6());
  TEST_CASE7();
  TEST_CASE8();
  EXIT_CHECK();
}
