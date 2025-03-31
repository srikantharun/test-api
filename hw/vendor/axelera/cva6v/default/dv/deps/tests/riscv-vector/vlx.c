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
  volatile uint8_t INP[] = {0xff, 0x00, 0x0f, 0xf0};
  __asm__ volatile("vloxei8.v v1, (%0), v2" ::"r"(INP));
  VCMP_U8(1, v1, 0xff, 0x00, 0x0f, 0xf0);
}

void TEST_CASE2(void) {
  VSET(4, e8, m1);
  VLOAD_8(v2, 0, 1, 2, 3);
  volatile int8_t INP[] = {0xff, 0x00, 0x0f, 0xf0};
  VLOAD_8(v0, 0x5, 0x0, 0x0, 0x0);
  VCLEAR(v1);
  __asm__ volatile("vloxei8.v v1, (%0), v2, v0.t" ::"r"(INP));
  VCMP_I8(2, v1, 0xff, 0x00, 0x0f, 0x00);
}

void TEST_CASE3(void) {
  VSET(3, e16, m1);
  VLOAD_16(v2, 0, 2, 4);
  volatile uint16_t INP[] = {0xffff, 0x0000, 0x0f0f, 0xf0f0};
  __asm__ volatile("vloxei16.v v1, (%0), v2" ::"r"(INP));
  VCMP_U16(3, v1, 0xffff, 0x0000, 0x0f0f);
}

void TEST_CASE4(void) {
  VSET(3, e16, m1);
  VLOAD_16(v2, 0, 2, 4);
  volatile int16_t INP[] = {0xffff, 0x0000, 0x0f0f, 0xf0f0};
  VLOAD_16(v0, 0x5, 0x0, 0x0, 0x0);
  VCLEAR(v1);
  __asm__ volatile("vloxei16.v v1, (%0), v2, v0.t" ::"r"(INP));
  VCMP_I16(4, v1, 0xffff, 0x0000, 0x0f0f);
}

void TEST_CASE5(void) {
  VSET(4, e32, m1);
  VLOAD_32(v2, 0, 4, 8, 12);
  volatile uint32_t INP[] = {0xffffffff, 0x00000000, 0x0f0f0f0f, 0xf0f0f0f0};
  __asm__ volatile("vloxei32.v v1, (%0), v2" ::"r"(INP));
  VCMP_U32(5, v1, 0xffffffff, 0x00000000, 0x0f0f0f0f, 0xf0f0f0f0);
}

void TEST_CASE6(void) {
  VSET(4, e32, m1);
  VLOAD_32(v2, 0, 4, 8, 12);
  volatile int32_t INP[] = {0xffffffff, 0x80000000, 0x0f0f0f0f, 0xf0f0f0f0};
  VLOAD_32(v0, 0x5, 0x0, 0x0, 0x0);
  VCLEAR(v1);
  __asm__ volatile(" vloxei32.v v1, (%0), v2, v0.t \n" ::"r"(INP));
  VCMP_I32(6, v1, 0xffffffff, 0x0, 0x0f0f0f0f, 0x0);
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
