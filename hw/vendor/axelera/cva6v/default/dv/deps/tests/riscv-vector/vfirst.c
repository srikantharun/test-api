// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1() {
  VSET(4, e32, m1);
  VLOAD_32(v2, 3);
  VLOAD_32(v0, 2, 0, 0, 0);
  volatile uint32_t scalar = 1337;
  volatile uint32_t OUP[]  = {0};
  __asm__ volatile(
      "vfirst.m %[A], v2, v0.t \n"
      "sw %[A], (%1) \n"
      :
      : [A] "r"(scalar), "r"(OUP));
  XCMP(1, OUP[0], 1);
}

void TEST_CASE2() {
  VSET(4, e32, m1);
  VLOAD_32(v2, 1, 2, 3, 4);
  VLOAD_32(v0, 0, 0, 0, 0);
  volatile int32_t scalar = 1337;
  volatile int32_t OUP[]  = {0};
  __asm__ volatile(
      "vfirst.m %[A], v2, v0.t \n"
      "sw %[A], (%1) \n"
      :
      : [A] "r"(scalar), "r"(OUP));
  XCMP(2, OUP[0], -1);
}

void TEST_CASE3() {
  VSET(4, e32, m1);
  VLOAD_32(v2, 4, 3, 2, 1);
  volatile int32_t scalar = 1337;
  volatile int32_t OUP[]  = {0};
  __asm__ volatile(
      "vfirst.m %[A], v2 \n"
      "sw %[A], (%1) \n"
      :
      : [A] "r"(scalar), "r"(OUP));
  XCMP(3, OUP[0], 2);
}

void TEST_CASE4() {
  VSET(4, e32, m1);
  VLOAD_32(v2, 0, 0, 0, 0);
  volatile int32_t scalar = 1337;
  volatile int32_t OUP[]  = {0};
  __asm__ volatile(
      "vfirst.m %[A], v2 \n"
      "sw %[A], (%1) \n"
      :
      : [A] "r"(scalar), "r"(OUP));
  XCMP(4, OUP[0], -1);
}

void TEST_CASE5() {
  VSET(0, e32, m1);
  volatile int32_t scalar = 1337;
  volatile int32_t OUP[]  = {0};
  __asm__ volatile(
      "vfirst.m %[A], v2 \n"
      "sw %[A], (%1) \n"
      :
      : [A] "r"(scalar), "r"(OUP));
  XCMP(5, OUP[0], -1);
}

int main(void) {
  INIT_CHECK();
  enable_vec();
  enable_fp();
  MASKED_TEST(TEST_CASE1());
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  TEST_CASE4();
  TEST_CASE5();
  EXIT_CHECK();
}
