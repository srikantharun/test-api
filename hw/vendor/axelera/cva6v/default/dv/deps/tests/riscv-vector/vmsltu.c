// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1(void) {
  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900);
  VLOAD_16(v3, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901);
  asm volatile("vmset.m v1");
  asm volatile("vmsltu.vv v1, v2, v3");
  VSET(2, e8, m1);
  VCMP_U8(1, v1, 0xAA, 0xAA);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900);
  VLOAD_32(v6, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901);
  asm volatile("vmset.m v2");
  asm volatile("vmsltu.vv v2, v4, v6");
  VSET(2, e8, m1);
  VCMP_U8(2, v2, 0xAA, 0xAA);
};

void TEST_CASE2(void) {
  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900);
  VLOAD_16(v3, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsltu.vv v1, v2, v3, v0.t");
  VSET(2, e8, m1);
  VCMP_U8(4, v1, 0xbb, 0xbb);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900, 12345, 80, 2560, 19900);
  VLOAD_32(v6, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901, 50, 7000, 400, 19901);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v2");
  asm volatile("vmsltu.vv v2, v4, v6, v0.t");
  VSET(2, e8, m1);
  VCMP_U8(5, v2, 0xbb, 0xbb);
};

void TEST_CASE3(void) {
  const uint64_t scalar = 40;

  VSET(16, e8, m1);
  VLOAD_8(v2, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199);
  asm volatile("vmset.m v1");
  asm volatile("vmsltu.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(7, v1, 0x66, 0x66);

  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  asm volatile("vmset.m v1");
  asm volatile("vmsltu.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(8, v1, 0x66, 0x66);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  asm volatile("vmset.m v2");
  asm volatile("vmsltu.vx v2, v4, %[A]" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(9, v2, 0x66, 0x66);
};

void TEST_CASE4(void) {
  const uint64_t scalar = 40;

  VSET(16, e8, m1);
  VLOAD_8(v2, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199, 123, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsltu.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(11, v1, 0x77, 0x77);

  VSET(16, e16, m1);
  VLOAD_16(v2, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v1");
  asm volatile("vmsltu.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(12, v1, 0x77, 0x77);

  VSET(16, e32, m2);
  VLOAD_32(v4, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199, 12345, 8, 25, 199);
  VLOAD_8(v0, 0xCC, 0xCC);
  asm volatile("vmset.m v2");
  asm volatile("vmsltu.vx v2, v4, %[A], v0.t" ::[A] "r"(scalar));
  VSET(2, e8, m1);
  VCMP_U8(13, v2, 0x77, 0x77);
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
