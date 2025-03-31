// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matteo Perotti <mperotti@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "vector_macros.h"

void TEST_CASE1(void) {
  VSET(16, e8, m1);
  VLOAD_8(v2, 0x9b, 0x28, 0xec, 0x86, 0x26, 0x85, 0xf7, 0x33, 0x46, 0x37, 0x2c, 0x0c, 0x8e, 0xae, 0xa1, 0x93);
  VLOAD_8(v3, 0x84, 0x5e, 0x3b, 0xdf, 0x10, 0xfc, 0x05, 0xcf, 0x42, 0xbe, 0x23, 0xdb, 0x37, 0x78, 0xe2, 0x85);
  asm volatile("vrem.vv v1, v2, v3");
  VCMP_I8(1, v1, 0x9b, 0x28, 0xec, 0xe9, 0x06, 0xfd, 0xfc, 0x02, 0x04, 0x37, 0x09, 0x0c, 0xfc, 0xae, 0xfb, 0x93);

  VSET(16, e16, m1);
  VLOAD_16(v2, 0xb58f, 0xa184, 0xdcf9, 0xd084, 0xbbc6, 0xcf0e, 0xbbd4, 0xa20c, 0xe04c, 0xd954, 0xda74, 0xa394, 0x207a,
           0x8975, 0xddd3, 0x897d);
  VLOAD_16(v3, 0x4534, 0xafd7, 0xf703, 0x92c2, 0x97e3, 0xd85a, 0x1540, 0x8c5c, 0x4a71, 0x43a7, 0xe65d, 0x2bdc, 0x497b,
           0x6aa0, 0x6071, 0xf431);
  asm volatile("vrem.vv v1, v2, v3");
  VCMP_I16(2, v1, 0xfac3, 0xf1ad, 0xf7f0, 0xd084, 0xbbc6, 0xf6b4, 0xfb94, 0xa20c, 0xe04c, 0xd954, 0xf417, 0xfb4c,
           0x207a, 0xf415, 0xddd3, 0xff93);

  VSET(16, e32, m2);
  VLOAD_32(v4, 0x620db972, 0x60b1f870, 0x7d1badcf, 0x90a85eb6, 0xca41954b, 0x10dc3772, 0xf7749e82, 0x027ed4d3,
           0xdcb6a562, 0xa979baf0, 0xb480c184, 0x979555c6, 0x3f894108, 0x803bd362, 0x9038beec, 0x22d7ca24);
  VLOAD_32(v6, 0xb9b52c0c, 0x30b52d8c, 0x832f89ea, 0x95181d9c, 0x85a6a24f, 0x2f2c64a7, 0xebe4120c, 0x83852646,
           0xfb1857b5, 0x25400571, 0xab2d7393, 0xddb87ac8, 0x01149cdf, 0x62b2c8dc, 0xaed39563, 0x41ec046e);
  asm volatile("vrem.vv v2, v4, v6");
  VCMP_I32(3, v2, 0x1bc2e57e, 0x2ffccae4, 0x004b37b9, 0xfb90411a, 0xca41954b, 0x10dc3772, 0xf7749e82, 0x027ed4d3,
           0xff0c3f6f, 0xf3f9c5d2, 0xb480c184, 0xfe6be56e, 0x00ddb682, 0xe2ee9c3e, 0xe1652989, 0x22d7ca24);
};

void TEST_CASE2(void) {
  VSET(16, e8, m1);
  VLOAD_8(v2, 0x9b, 0x28, 0xec, 0x86, 0x26, 0x85, 0xf7, 0x33, 0x46, 0x37, 0x2c, 0x0c, 0x8e, 0xae, 0xa1, 0x93);
  VLOAD_8(v3, 0x84, 0x5e, 0x3b, 0xdf, 0x10, 0xfc, 0x05, 0xcf, 0x42, 0xbe, 0x23, 0xdb, 0x37, 0x78, 0xe2, 0x85);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vrem.vv v1, v2, v3, v0.t");
  VCMP_I8(5, v1, 0, 0x28, 0, 0xe9, 0, 0xfd, 0, 0x02, 0, 0x37, 0, 0x0c, 0, 0xae, 0, 0x93);

  VSET(16, e16, m1);
  VLOAD_16(v2, 0xb58f, 0xa184, 0xdcf9, 0xd084, 0xbbc6, 0xcf0e, 0xbbd4, 0xa20c, 0xe04c, 0xd954, 0xda74, 0xa394, 0x207a,
           0x8975, 0xddd3, 0x897d);
  VLOAD_16(v3, 0x4534, 0xafd7, 0xf703, 0x92c2, 0x97e3, 0xd85a, 0x1540, 0x8c5c, 0x4a71, 0x43a7, 0xe65d, 0x2bdc, 0x497b,
           0x6aa0, 0x6071, 0xf431);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vrem.vv v1, v2, v3, v0.t");
  VCMP_I16(6, v1, 0, 0xf1ad, 0, 0xd084, 0, 0xf6b4, 0, 0xa20c, 0, 0xd954, 0, 0xfb4c, 0, 0xf415, 0, 0xff93);

  VSET(16, e32, m2);
  VLOAD_32(v4, 0x620db972, 0x60b1f870, 0x7d1badcf, 0x90a85eb6, 0xca41954b, 0x10dc3772, 0xf7749e82, 0x027ed4d3,
           0xdcb6a562, 0xa979baf0, 0xb480c184, 0x979555c6, 0x3f894108, 0x803bd362, 0x9038beec, 0x22d7ca24);
  VLOAD_32(v6, 0xb9b52c0c, 0x30b52d8c, 0x832f89ea, 0x95181d9c, 0x85a6a24f, 0x2f2c64a7, 0xebe4120c, 0x83852646,
           0xfb1857b5, 0x25400571, 0xab2d7393, 0xddb87ac8, 0x01149cdf, 0x62b2c8dc, 0xaed39563, 0x41ec046e);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v2);
  asm volatile("vrem.vv v2, v4, v6, v0.t");
  VCMP_I32(7, v2, 0, 0x2ffccae4, 0, 0xfb90411a, 0, 0x10dc3772, 0, 0x027ed4d3, 0, 0xf3f9c5d2, 0, 0xfe6be56e, 0,
           0xe2ee9c3e, 0, 0x22d7ca24);
};

void TEST_CASE3(void) {
  VSET(16, e8, m1);
  VLOAD_8(v2, 0x5b, 0x3b, 0xc4, 0x95, 0x41, 0x71, 0x9b, 0x67, 0x84, 0x2e, 0x0a, 0x2a, 0xb2, 0x57, 0xe5, 0x6c);
  int64_t scalar = 5;
  asm volatile("vrem.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_I8(9, v1, 0x01, 0x04, 0x00, 0xfe, 0x00, 0x03, 0xff, 0x03, 0xfc, 0x01, 0x00, 0x02, 0xfd, 0x02, 0xfe, 0x03);

  VSET(16, e16, m1);
  VLOAD_16(v2, 0xc670, 0x8f3b, 0x200f, 0x52ea, 0xfdce, 0xcf06, 0x57f1, 0x1936, 0xb6ec, 0x69e8, 0x0abf, 0x441e, 0xa420,
           0x396c, 0xe7c9, 0xa464);
  scalar = -538;
  asm volatile("vrem.vx v1, v2, %[A]" ::[A] "r"(scalar));
  VCMP_I16(10, v1, 0xff2e, 0xfe9d, 0x0089, 0x00f4, 0xffe8, 0xff5c, 0x01c7, 0x0218, 0xfe60, 0x00d4, 0x003d, 0x00de,
           0xfe7e, 0x00ae, 0xfee7, 0xfec2);

  VSET(16, e32, m2);
  VLOAD_32(v4, 0xf937dbf9, 0x6d855b59, 0x3bd09126, 0xaed11886, 0x6eb6f4bd, 0x5c639253, 0xca0f2abf, 0x57fec97b,
           0x39496099, 0x8bfcdd58, 0x0f19f6e2, 0x2070c8d4, 0x8c689324, 0x2eecd9d7, 0xe2907e94, 0xb6cc2d44);
  scalar = 649;
  asm volatile("vrem.vx v2, v4, %[A]" ::[A] "r"(scalar));
  VCMP_I32(11, v2, 0xfffffee4, 0x00000116, 0x00000160, 0xffffffef, 0x00000217, 0x00000275, 0xfffffea6, 0x000000a9,
           0x000000e4, 0xfffffe09, 0x00000272, 0x0000023c, 0xffffff79, 0x000000ce, 0xffffffb3, 0xfffffe0e);
};

void TEST_CASE4(void) {
  VSET(16, e8, m1);
  VLOAD_8(v2, 0x5b, 0x3b, 0xc4, 0x95, 0x41, 0x71, 0x9b, 0x67, 0x84, 0x2e, 0x0a, 0x2a, 0xb2, 0x57, 0xe5, 0x6c);
  int64_t scalar = 5;
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vrem.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_I8(13, v1, 0, 0x04, 0, 0xfe, 0, 0x03, 0, 0x03, 0, 0x01, 0, 0x02, 0, 0x02, 0, 0x03);

  VSET(16, e16, m1);
  VLOAD_16(v2, 0xc670, 0x8f3b, 0x200f, 0x52ea, 0xfdce, 0xcf06, 0x57f1, 0x1936, 0xb6ec, 0x69e8, 0x0abf, 0x441e, 0xa420,
           0x396c, 0xe7c9, 0xa464);
  scalar = -538;
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vrem.vx v1, v2, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_I16(14, v1, 0, 0xfe9d, 0, 0x00f4, 0, 0xff5c, 0, 0x0218, 0, 0x00d4, 0, 0x00de, 0, 0x00ae, 0, 0xfec2);

  VSET(16, e32, m2);
  VLOAD_32(v4, 0xf937dbf9, 0x6d855b59, 0x3bd09126, 0xaed11886, 0x6eb6f4bd, 0x5c639253, 0xca0f2abf, 0x57fec97b,
           0x39496099, 0x8bfcdd58, 0x0f19f6e2, 0x2070c8d4, 0x8c689324, 0x2eecd9d7, 0xe2907e94, 0xb6cc2d44);
  scalar = 649;
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v2);
  asm volatile("vrem.vx v2, v4, %[A], v0.t" ::[A] "r"(scalar));
  VCMP_I32(15, v2, 0, 0x00000116, 0, 0xffffffef, 0, 0x00000275, 0, 0x000000a9, 0, 0xfffffe09, 0, 0x0000023c, 0,
           0x000000ce, 0, 0xfffffe0e);
};

int main(void) {
  INIT_CHECK();
  enable_vec();

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  EXIT_CHECK();
}
