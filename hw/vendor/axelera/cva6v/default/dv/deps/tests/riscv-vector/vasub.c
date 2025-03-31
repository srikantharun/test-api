// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1(void) {
  set_vxrm(0);  // setting vxrm to rnu rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 5, 10, 15, 20);
  VLOAD_32(v2, -1, 2, -3, 4);
  __asm__ volatile("vasub.vv v3, v1, v2" ::);
  VCMP_U32(1, v3, 3, 4, 9, 8);
}

void TEST_CASE2(void) {
  set_vxrm(0);  // setting vxrm to rnu rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 5, 10, 15, 20);
  VLOAD_32(v2, 1, 2, 3, -4);
  VLOAD_32(v0, 10, 0, 0, 0);
  VCLEAR(v3);
  __asm__ volatile("vasub.vv v3, v1, v2, v0.t" ::);
  VCMP_U32(2, v3, 0, 4, 0, 12);
}

void TEST_CASE3(void) {
  set_vxrm(0);  // setting vxrm to rnu rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 5, 10, 15, 20);
  const uint64_t scalar = -5;
  __asm__ volatile("vasub.vx v3, v1, %[A]" ::[A] "r"(scalar));
  VCMP_U32(3, v3, 5, 8, 10, 13);
}

void TEST_CASE4(void) {
  set_vxrm(0);  // setting vxrm to rnu rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 5, 10, 15, 20);
  const uint64_t scalar = -5;
  VLOAD_32(v0, 10, 0, 0, 0);
  VCLEAR(v3);
  __asm__ volatile("vasub.vx v3, v1, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U32(4, v3, 0, 8, 0, 13);
}

void TEST_CASE5(void) {
  set_vxrm(1);  // setting vxrm to rne rounding mode
  VSET(4, e8, m1);
  VLOAD_8(v1, 1, -2, -3, 4);
  VLOAD_8(v2, -1, -9, 3, -5);
  VLOAD_8(v0, 0xA, 0x0, 0x0, 0x0);
  VCLEAR(v3);
  __asm__ volatile("vasub.vv v3, v1, v2, v0.t" ::);
  VCMP_U8(5, v3, 0, 4, 0, 4);
}

void TEST_CASE6(void) {
  set_vxrm(2);  // setting vxrm to rdn rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 1, -2, 3, -4);
  const uint64_t scalar = -5;
  __asm__ volatile("vasub.vx v3, v1, %[A]" ::[A] "r"(scalar));
  VCMP_U32(6, v3, 3, 1, 4, 0);
}

void TEST_CASE7(void) {
  set_vxrm(3);  // setting vxrm to rod rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 1, 2, 3, 4);
  const uint64_t scalar = -5;
  VLOAD_32(v0, 0xA, 0x0, 0x0, 0x0);
  VCLEAR(v3);
  __asm__ volatile("vasub.vx v3, v1, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U32(7, v3, 0, 3, 0, 5);
}

void TEST_CASE8(void) {
  set_vxrm(0);  // setting vxrm to rnu rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v1, 5, 10, 15, 20);
  VLOAD_32(v2, -1, 2, -3, 4);
  __asm__ volatile("vasub.vv v2, v1, v2" ::);
  VCMP_U32(8, v2, 3, 4, 9, 8);
}

void TEST_CASE9(void) {
  set_vxrm(0);  // setting vxrm to rnu rounding mode
  VSET(4, e32, m1);
  VLOAD_32(v2, -1, 2, -3, 4);
  __asm__ volatile("vasub.vv v1, v1, v1" ::);
  VCMP_U32(9, v1, 0, 0, 0, 0);
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());
  MASKED_TEST(TEST_CASE5());
  TEST_CASE6();
  MASKED_TEST(TEST_CASE7());
  TEST_CASE8();
  TEST_CASE9();
  EXIT_CHECK();
}
