// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(16, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v1, v2, 3");
  VCMP_U8(1, v1, -1, -1, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);

  VSET(16, e16, m1);
  VLOAD_16(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_16(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v1, v2, 4");
  VCMP_U16(2, v1, -1, -1, -1, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);

  VSET(16, e32, m2);
  VLOAD_32(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_32(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v2, v4, 5");
  VCMP_U32(3, v2, -1, -1, -1, -1, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
}

void TEST_CASE2() {
  VSET(16, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslideup.vi v1, v2, 3, v0.t");
  VCMP_U8(5, v1, -1, -1, -1, 1, -1, 3, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13);

  VSET(16, e16, m1);
  VLOAD_16(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_16(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v1, v2, 4, v0.t");
  VCMP_U16(6, v1, -1, -1, -1, -1, -1, 2, -1, 4, -1, 6, -1, 8, -1, 10, -1, 12);

  VSET(16, e32, m2);
  VLOAD_32(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_32(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v2, v4, 5, v0.t");
  VCMP_U32(7, v2, -1, -1, -1, -1, -1, 1, -1, 3, -1, 5, -1, 7, -1, 9, -1, 11);
}

void TEST_CASE3() {
  uint64_t scalar = 3;

  VSET(16, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U8(9, v1, -1, -1, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);

  VSET(16, e16, m1);
  VLOAD_16(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_16(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U16(10, v1, -1, -1, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);

  VSET(16, e32, m2);
  VLOAD_32(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_32(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vx v2, v4, %[A]" ::[A] "r"(scalar));
  VCMP_U32(11, v2, -1, -1, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
}

void TEST_CASE4() {
  uint64_t scalar = 3;

  VSET(16, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslideup.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U8(13, v1, -1, -1, -1, 1, -1, 3, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13);

  VSET(16, e16, m1);
  VLOAD_16(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_16(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslideup.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U16(14, v1, -1, -1, -1, 1, -1, 3, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13);

  VSET(16, e32, m2);
  VLOAD_32(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_32(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslideup.vx v2, v4, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U32(15, v2, -1, -1, -1, 1, -1, 3, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13);
}

// Stress the masked VSLIDEUP to enforce that the used mask bit indices should
// follow the output vector element indices and not the input ones
void TEST_CASE5() {
  VSET(16, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0x80);
  asm volatile("vslideup.vi v1, v2, 3, v0.t");
  VCMP_U8(17, v1, -1, -1, -1, 1, -1, 3, -1, 5, -1, -1, -1, -1, -1, -1, -1, 13);

  VSET(16, e16, m1);
  VLOAD_16(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_16(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v1, v2, 4, v0.t");
  VCMP_U16(18, v1, -1, -1, -1, -1, -1, 2, -1, 4, -1, -1, -1, -1, -1, -1, -1, 12);

  VSET(16, e32, m2);
  VLOAD_32(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  VLOAD_32(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslideup.vi v2, v4, 5, v0.t");
  VCMP_U32(19, v2, -1, -1, -1, -1, -1, 1, -1, 3, -1, -1, -1, -1, -1, -1, -1, 11);
}

int main(void) {
  INIT_CHECK();
  enable_vec();

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());
  MASKED_TEST(TEST_CASE5());

  EXIT_CHECK();
}
