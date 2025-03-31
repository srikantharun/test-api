// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1(void) {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0, 1, 2, 3);
  volatile uint8_t OUP[] = {0xef, 0xef, 0xef, 0xef};
  VLOAD_8(v1, 0xff, 0x00, 0xf0, 0x0f);
  __asm__ volatile("vsuxei8.v v1, (%0), v2" ::"r"(OUP));
  VVCMP_U8(1, OUP, 0xff, 0x00, 0xf0, 0x0f);
}

void TEST_CASE2(void) {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0, 1, 2, 3);
  volatile uint8_t OUP[] = {0xef, 0xef, 0xef, 0xef};
  VLOAD_8(v1, 0xff, 0x00, 0xf0, 0x0f);
  VLOAD_8(v0, 0x12, 0x0, 0x0, 0x0);
  __asm__ volatile("vsuxei8.v v1, (%0), v2, v0.t" ::"r"(OUP));
  VVCMP_U8(2, OUP, 0xef, 0x00, 0xef, 0xef);
}

void TEST_CASE3(void) {
  VSET(4, e16, m1);
  VLOAD_16(v2, 0, 2, 4, 6);
  volatile uint16_t OUP[] = {0xdead, 0xbeef, 0xdead, 0xbeef};
  VLOAD_16(v1, 0xffff, 0x0000, 0xf0f0, 0x0f0f);
  __asm__ volatile("vsuxei16.v v1, (%0), v2" ::"r"(OUP));
  VVCMP_U16(3, OUP, 0xffff, 0x0000, 0xf0f0, 0x0f0f);
}

void TEST_CASE4(void) {
  VSET(4, e16, m1);
  VLOAD_16(v2, 0, 2, 4, 6);
  volatile uint16_t OUP[] = {0xdead, 0xbeef, 0xdead, 0xbeef};
  VLOAD_16(v1, 0xffff, 0x0000, 0xf0f0, 0x0f0f);
  VLOAD_16(v0, 0x12, 0x0, 0x0, 0x0);
  __asm__ volatile("vsuxei16.v v1, (%0), v2, v0.t" ::"r"(OUP));
  VVCMP_U16(4, OUP, 0xdead, 0x0000, 0xdead, 0xbeef);
}

void TEST_CASE5(void) {
  VSET(4, e32, m1);
  VLOAD_32(v2, 0, 4, 8, 12);
  volatile uint32_t OUP[] = {0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef};
  VLOAD_32(v1, 0xffffffff, 0x00000000, 0xf0f0f0f0, 0x0f0f0f0f);
  __asm__ volatile("vsuxei32.v v1, (%0), v2" ::"r"(OUP));
  VVCMP_U32(5, OUP, 0xffffffff, 0x00000000, 0xf0f0f0f0, 0x0f0f0f0f);
}

void TEST_CASE6(void) {
  VSET(4, e32, m1);
  VLOAD_32(v2, 0, 4, 8, 12);
  volatile uint32_t OUP[] = {0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef};
  VLOAD_32(v1, 0xffffffff, 0x00000000, 0xf0f0f0f0, 0x0f0f0f0f);
  VLOAD_32(v0, 0x12, 0x0, 0x0, 0x0);
  __asm__ volatile("vsuxei32.v v1, (%0), v2, v0.t" ::"r"(OUP));
  VVCMP_U32(6, OUP, 0xdeadbeef, 0x00000000, 0xdeadbeef, 0xdeadbeef);
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
  EXIT_CHECK();
}
