// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(32, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
          30, 31, 32);
  VSET(16, e8, m1);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vi v1, v2, 3");
  VCMP_U8(1, v1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);

  VSET(32, e16, m2);
  VLOAD_16(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e16, m2);
  VLOAD_16(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vi v2, v4, 4");
  VCMP_U16(2, v2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20);

  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vi v4, v8, 5");
  VCMP_U32(3, v4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21);
}

void TEST_CASE2() {
  VSET(32, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
          30, 31, 32);
  VSET(16, e8, m1);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslidedown.vi v1, v2, 3, v0.t");
  VCMP_U8(5, v1, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13, -1, 15, -1, 17, -1, 19);

  VSET(32, e16, m2);
  VLOAD_16(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e16, m2);
  VLOAD_16(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vi v2, v4, 4, v0.t");
  VCMP_U16(6, v2, -1, 6, -1, 8, -1, 10, -1, 12, -1, 14, -1, 16, -1, 18, -1, 20);

  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vi v4, v8, 5, v0.t");
  VCMP_U32(7, v4, -1, 7, -1, 9, -1, 11, -1, 13, -1, 15, -1, 17, -1, 19, -1, 21);
}

void TEST_CASE3() {
  uint64_t scalar = 3;

  VSET(32, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
          30, 31, 32);
  VSET(16, e8, m1);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U8(9, v1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);

  VSET(32, e16, m2);
  VLOAD_16(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e16, m2);
  VLOAD_16(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vx v2, v4, %[A]" ::[A] "r"(scalar));
  VCMP_U16(10, v2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);

  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vx v4, v8, %[A]" ::[A] "r"(scalar));
  VCMP_U32(11, v4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);
}

void TEST_CASE4() {
  uint64_t scalar = 3;

  VSET(32, e8, m1);
  VLOAD_8(v2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
          30, 31, 32);
  VSET(16, e8, m1);
  VLOAD_8(v1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslidedown.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U8(13, v1, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13, -1, 15, -1, 17, -1, 19);

  VSET(32, e16, m2);
  VLOAD_16(v4, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e16, m2);
  VLOAD_16(v2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslidedown.vx v2, v4, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U16(14, v2, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13, -1, 15, -1, 17, -1, 19);

  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(16, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslidedown.vx v4, v8, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U32(15, v4, -1, 5, -1, 7, -1, 9, -1, 11, -1, 13, -1, 15, -1, 17, -1, 19);
}

void TEST_CASE5() {
  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(12, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vi v4, v8, 7");
  VCMP_U32(17, v4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);
}

void TEST_CASE6() {
  // fill source vector register and everything beyond with non-zero value
  uint64_t vl;
  asm volatile("vsetvli %0, x0, e8, m8, ta, ma" : "=r"(vl));
  asm volatile("vmv.v.i v8, 1");
  asm volatile("vmv.v.i v16, 1");
  asm volatile("vmv.v.i v24, 1");

  uint64_t scalar = 65536;  // offset value exceeding any possible VLMAX
  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(12, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  asm volatile("vslidedown.vx v4, v8, %[A]" ::[A] "r"(scalar));
  VCMP_U32(17, v4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}

void TEST_CASE7() {
  // fill source vector register and everything beyond with non-zero value
  uint64_t vl;
  asm volatile("vsetvli %0, x0, e8, m8, ta, ma" : "=r"(vl));
  asm volatile("vmv.v.i v8, 1");
  asm volatile("vmv.v.i v16, 1");
  asm volatile("vmv.v.i v24, 1");

  uint64_t scalar = 65536;  // offset value exceeding any possible VLMAX
  VSET(32, e32, m4);
  VLOAD_32(v8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
           29, 30, 31, 32);
  VSET(12, e32, m4);
  VLOAD_32(v4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vslidedown.vx v4, v8, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U32(19, v4, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0);
}

int main(void) {
  INIT_CHECK();
  enable_vec();

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  TEST_CASE5();
  TEST_CASE6();
  MASKED_TEST(TEST_CASE7());

  EXIT_CHECK();
}
