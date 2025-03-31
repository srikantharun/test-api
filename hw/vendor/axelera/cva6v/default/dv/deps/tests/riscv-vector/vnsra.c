// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1(void) {
  VSET(16, e8, m1);
  VLOAD_16(v2, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00,
           0xFF00, 0xFF00, 0xFF00);
  VLOAD_8(v3, 0, 1, 2, 3, 7, 15, 31, 32, 0, 1, 2, 3, 7, 15, 31, 32);
  asm volatile("vnsra.wv v4, v2, v3");
  VCMP_U8(1, v4, 0x00, 0x80, 0xC0, 0xE0, 0xFE, 0xFF, 0xFF, 0x00, 0x00, 0x80, 0xC0, 0xE0, 0xFE, 0xFF, 0xFF, 0x00);

  VSET(16, e16, m1);
  VLOAD_32(v2, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000,
           0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000);
  VLOAD_16(v6, 0, 1, 2, 3, 7, 15, 31, 32, 0, 1, 2, 3, 7, 15, 31, 32);
  asm volatile("vnsra.wv v4, v2, v6");
  VCMP_U16(2, v4, 0x0000, 0x8000, 0xC000, 0xE000, 0xFE00, 0xFFFE, 0xFFFF, 0x0000, 0x0000, 0x8000, 0xC000, 0xE000,
           0xFE00, 0xFFFE, 0xFFFF, 0x0000);
};

void TEST_CASE2(void) {
  VSET(16, e8, m1);
  VLOAD_16(v2, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00,
           0xFF00, 0xFF00, 0xFF00);
  VLOAD_8(v3, 0, 1, 2, 3, 7, 15, 31, 32, 0, 1, 2, 3, 7, 15, 31, 32);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vnsra.wv v4, v2, v3, v0.t");
  VCMP_U8(4, v4, 0x00, 0x80, 0x00, 0xE0, 0x00, 0xFF, 0x00, 0x00, 0x00, 0x80, 0x00, 0xE0, 0x00, 0xFF, 0x00, 0x00);

  VSET(16, e16, m1);
  VLOAD_32(v2, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000,
           0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000, 0xFFFF0000);
  VLOAD_16(v6, 0, 1, 2, 3, 7, 15, 31, 32, 0, 1, 2, 3, 7, 15, 31, 32);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vnsra.wv v4, v2, v6, v0.t");
  VCMP_U16(5, v4, 0x0000, 0x8000, 0x0000, 0xE000, 0x0000, 0xFFFE, 0x0000, 0x0000, 0x0000, 0x8000, 0x0000, 0xE000,
           0x0000, 0xFFFE, 0x0000, 0x0000);
};

void TEST_CASE3(void) {
  const uint64_t scalar = 2;

  VSET(16, e8, m1);
  VLOAD_16(v2, 0x0004, 0x0008, 0x000C, 0x0010, 0x0014, 0x0018, 0x001C, 0x0020, 0xFFE0, 0xFFE4, 0xFFE8, 0xFFEC, 0xFFF0,
           0xFFF4, 0xFFF8, 0xFFFC);
  asm volatile("vnsra.wx v4, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U8(7, v4, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF);

  VSET(16, e16, m1);
  VLOAD_32(v2, 0x00000004, 0x00000008, 0x0000000C, 0x00000010, 0x00000014, 0x00000018, 0x0000001C, 0x00000020,
           0xFFFFFFE0, 0xFFFFFFE4, 0xFFFFFFE8, 0xFFFFFFEC, 0xFFFFFFF0, 0xFFFFFFF4, 0xFFFFFFF8, 0xFFFFFFFC);
  asm volatile("vnsra.wx v4, v2, %[A]" ::[A] "r"(scalar));
  VCMP_U16(8, v4, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007, 0x0008, 0xFFF8, 0xFFF9, 0xFFFA, 0xFFFB,
           0xFFFC, 0xFFFD, 0xFFFE, 0xFFFF);
};

void TEST_CASE4(void) {
  const uint64_t scalar = 2;

  VSET(16, e8, m1);
  VLOAD_16(v2, 0x0004, 0x0008, 0x000C, 0x0010, 0x0014, 0x0018, 0x001C, 0x0020, 0xFFE0, 0xFFE4, 0xFFE8, 0xFFEC, 0xFFF0,
           0xFFF4, 0xFFF8, 0xFFFC);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vnsra.wx v4, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U8(10, v4, 0x00, 0x02, 0x00, 0x04, 0x00, 0x06, 0x00, 0x08, 0x00, 0xF9, 0x00, 0xFB, 0x00, 0xFD, 0x00, 0xFF);

  VSET(16, e16, m1);
  VLOAD_32(v2, 0x00000004, 0x00000008, 0x0000000C, 0x00000010, 0x00000014, 0x00000018, 0x0000001C, 0x00000020,
           0xFFFFFFE0, 0xFFFFFFE4, 0xFFFFFFE8, 0xFFFFFFEC, 0xFFFFFFF0, 0xFFFFFFF4, 0xFFFFFFF8, 0xFFFFFFFC);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vnsra.wx v4, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_U16(11, v4, 0x0000, 0x0002, 0x0000, 0x0004, 0x0000, 0x0006, 0x0000, 0x0008, 0x0000, 0xFFF9, 0x0000, 0xFFFB,
           0x0000, 0xFFFD, 0x0000, 0xFFFF);
};

void TEST_CASE5(void) {
  VSET(16, e8, m1);
  VLOAD_16(v2, 0x0004, 0x0008, 0x000C, 0x0010, 0x0014, 0x0018, 0x001C, 0x0020, 0xFFE0, 0xFFE4, 0xFFE8, 0xFFEC, 0xFFF0,
           0xFFF4, 0xFFF8, 0xFFFC);
  asm volatile("vnsra.wi v4, v2, 2");
  VCMP_U8(13, v4, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF);

  VSET(16, e16, m1);
  VLOAD_32(v2, 0x00000004, 0x00000008, 0x0000000C, 0x00000010, 0x00000014, 0x00000018, 0x0000001C, 0x00000020,
           0xFFFFFFE0, 0xFFFFFFE4, 0xFFFFFFE8, 0xFFFFFFEC, 0xFFFFFFF0, 0xFFFFFFF4, 0xFFFFFFF8, 0xFFFFFFFC);
  asm volatile("vnsra.wi v4, v2, 2");
  VCMP_U16(14, v4, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007, 0x0008, 0xFFF8, 0xFFF9, 0xFFFA, 0xFFFB,
           0xFFFC, 0xFFFD, 0xFFFE, 0xFFFF);
};

void TEST_CASE6(void) {
  VSET(16, e8, m1);
  VLOAD_16(v2, 0x0004, 0x0008, 0x000C, 0x0010, 0x0014, 0x0018, 0x001C, 0x0020, 0xFFE0, 0xFFE4, 0xFFE8, 0xFFEC, 0xFFF0,
           0xFFF4, 0xFFF8, 0xFFFC);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vnsra.wi v4, v2, 2, v0.t");
  VCMP_U8(16, v4, 0x00, 0x02, 0x00, 0x04, 0x00, 0x06, 0x00, 0x08, 0x00, 0xF9, 0x00, 0xFB, 0x00, 0xFD, 0x00, 0xFF);

  VSET(16, e16, m1);
  VLOAD_32(v2, 0x00000004, 0x00000008, 0x0000000C, 0x00000010, 0x00000014, 0x00000018, 0x0000001C, 0x00000020,
           0xFFFFFFE0, 0xFFFFFFE4, 0xFFFFFFE8, 0xFFFFFFEC, 0xFFFFFFF0, 0xFFFFFFF4, 0xFFFFFFF8, 0xFFFFFFFC);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vnsra.wi v4, v2, 2, v0.t");
  VCMP_U16(17, v4, 0x0000, 0x0002, 0x0000, 0x0004, 0x0000, 0x0006, 0x0000, 0x0008, 0x0000, 0xFFF9, 0x0000, 0xFFFB,
           0x0000, 0xFFFD, 0x0000, 0xFFFF);
};

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
