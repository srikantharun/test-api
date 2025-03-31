// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Muhammad Ijaz

#include "vector_macros.h"

void TEST_CASE1() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 800, 65535, -50, 25);
  VLOAD_8(v4, 7, 7, 7, 7);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wv v1, v2, v4");
  VCMP_U8(1, v1, 6, 0xff, 0xff, 0);
  read_vxsat(vxsat);
  check_vxsat(1, vxsat, 1);
  reset_vxsat;
}

void TEST_CASE2() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 800, 65535, -50, 25);
  VLOAD_8(v4, 7, 7, 7, 7);
  VLOAD_8(v0, 0x5, 0, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wv v1, v2, v4, v0.t");
  VCMP_U8(2, v1, 6, 0, 0xff, 0);
  read_vxsat(vxsat);
  check_vxsat(2, vxsat, 1);
  reset_vxsat;
}

void TEST_CASE3() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 800, 65535, -50, 25);
  int8_t scalar = 7;
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U8(3, v1, 6, 0xff, 0xff, 0);
  read_vxsat(vxsat);
  check_vxsat(3, vxsat, 1);
  reset_vxsat;
}

void TEST_CASE4() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 800, 65535, -50, 25);
  int8_t scalar = 7;
  VLOAD_8(v0, 0x5, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U8(4, v1, 6, 0, 0xff, 0);
  read_vxsat(vxsat);
  check_vxsat(4, vxsat, 1);
  reset_vxsat;
}

void TEST_CASE5() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 800, 65535, -50, 25);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wi v1, v2, 7");
  VCMP_U8(5, v1, 6, 0xff, 0xff, 0);
  read_vxsat(vxsat);
  check_vxsat(5, vxsat, 1);
  reset_vxsat;
}

void TEST_CASE6() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 800, 65535, -50, 25);
  VLOAD_8(v0, 0x5, 0, 0, 0);
  VCLEAR(v1);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wi v1, v2, 7, v0.t");
  VCMP_U8(6, v1, 6, 0, 0xff, 0);
  read_vxsat(vxsat);
  check_vxsat(6, vxsat, 1);
  reset_vxsat;
}

// saturate while shifting
void TEST_CASE7() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 0x5555, 0xAAAA, 0x5555, 0xAAAA);
  VLOAD_8(v4, 5, 5, 6, 6);
  __asm__ volatile("csrw vxrm, 2");
  __asm__ volatile("vnclipu.wv v1, v2, v4");
  VCMP_I8(7, v1, 0xFF, 0xFF, 0xFF, 0xFF);
  read_vxsat(vxsat);
  check_vxsat(7, vxsat, 1);
  reset_vxsat;
}

// saturate while rounding
void TEST_CASE8() {
  uint64_t vxsat;
  VSET(4, e8, m1);
  VLOAD_16(v2, 0x8000, 0xFF00, 0x80FF, 0xFFFF);
  int8_t scalar = 8;
  __asm__ volatile("csrw vxrm, 0");
  __asm__ volatile("vnclipu.wx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_I8(8, v1, 0x80, 0xFF, 0x81, 0xFF);
  read_vxsat(vxsat);
  check_vxsat(8, vxsat, 1);
  reset_vxsat;
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
