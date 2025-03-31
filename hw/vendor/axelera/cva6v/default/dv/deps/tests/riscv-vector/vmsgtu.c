// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1(void) {
  const uint64_t scalar = 40;

  VSET(16, e8, m1);
  VLOAD_8(v2, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(1, v1, 0x99, 0x99);

  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(2, v1, 0x99, 0x99);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  asm volatile("vmset.m v2");
  asm volatile("vmsgtu.vx v2, v4, %[A]" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(3, v2, 0x99, 0x99);
};

void TEST_CASE2(void) {
  const uint64_t scalar = 40;

  VSET(16, e8, m1);
  VLOAD_8(v2, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(5, v1, 0xbb, 0xbb);

  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(6, v1, 0xbb, 0xbb);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v2");
  asm volatile("vmsgtu.vx v2, v4, %[A], v0.t" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(7, v2, 0xbb, 0xbb);
};

void TEST_CASE3(void) {
  VSET(16, e8, m1);
  VLOAD_8(v2, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vi v1, v2, 15");
  VSET(2, e8, m1);
  VCMP_U8(9, v1, 0xDD, 0xDD);

  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vi v1, v2, 15");
  VSET(2, e8, m1);
  VCMP_U8(10, v1, 0xDD, 0xDD);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  asm volatile("vmset.m v2");
  asm volatile("vmsgtu.vi v2, v4, 15");
  VSET(2, e8, m1);
  VCMP_U8(11, v2, 0xDD, 0xDD);
};

void TEST_CASE4(void) {
  VSET(16, e8, m1);
  VLOAD_8(v2, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vi v1, v2, 15, v0.t");
  VSET(2, e8, m1);
  VCMP_U8(13, v1, 0xff, 0xff);

  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsgtu.vi v1, v2, 15, v0.t");
  VSET(2, e8, m1);
  VCMP_U8(14, v1, 0xff, 0xff);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v2");
  asm volatile("vmsgtu.vi v2, v4, 15, v0.t");
  VSET(2, e8, m1);
  VCMP_U8(15, v2, 0xff, 0xff);
};

int main(void) {
  INIT_CHECK();
  enable_vec();

  VSET(1, e16, m1);
  VCLEAR(v0);
  VCLEAR(v1);
  VCLEAR(v2);
  VCLEAR(v3);

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  EXIT_CHECK();
}
