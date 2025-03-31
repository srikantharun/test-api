// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matteo Perotti <mperotti@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

/////////////////
// vfncvt.xu.f //
/////////////////

// Simple random test with similar values
void TEST_CASE1(void) {
  VSET(16, e16, m1);
  //                9165.669,   5488.131,  -1648.302,  80154.047,   7163.093,
  //                -6826.076,  -6976.746,   2675.899,   9587.624, -3671.810,
  //                3611.960, -9086.531, -5333.617, -3284.205,   5676.141,
  //                -8293.472
  VLOAD_32(v2, 0x460f36ad, 0x45ab810c, 0x479c8d06, 0xc59cf316, 0x45dfd8be, 0xc5d5509c, 0xc5da05f8, 0x45273e62,
           0x4615ce7f, 0xc5657cf5, 0x4561bf5b, 0xc60dfa20, 0xc5a6acf0, 0xc54d4347, 0x45b16120, 0xc60195e3);
  asm volatile("vfncvt.xu.f.w v4, v2");
  //                    9166,       5488,      65535,          0,       7163, 0,
  //                    0,       2676,       9588,          0,       3612, 0, 0,
  //                    0,       5676,          0
  VCMP_U16(1, v4, 0x23ce, 0x1570, 0xffff, 0x0000, 0x1bfb, 0x0000, 0x0000, 0x0a74, 0x2574, 0x0000, 0x0e1c, 0x0000,
           0x0000, 0x0000, 0x162c, 0x0000);

  VSET(16, e8, m1);
  // 0.000000, 134.237000, 12.473999, 0.711000, 134.947998,
  // 13.184998, 1.422000, 135.658997, 13.895996, 2.133000,
  // 136.369995, 14.606995, 2.844000, 137.080994, 15.317993, 3.555000
  VLOAD_16(v2, 0x0000, 0x5832, 0x4a3d, 0x39b0, 0x5838, 0x4a98, 0x3db0, 0x583d, 0x4af3, 0x4044, 0x5843, 0x4b4e, 0x41b0,
           0x5849, 0x4ba9, 0x431c);
  asm volatile("vfncvt.xu.f.w v4, v2");
  VCMP_U8(2, v4, 0x00, 0x86, 0x0c, 0x01, 0x87, 0x0d, 0x01, 0x88, 0x0e, 0x02, 0x88, 0x0f, 0x03, 0x89, 0x0f, 0x04);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //                    9165.669,       5488.131,      -1648.302, -5022.386,
  //                    7163.093, -6826.076, -6976.746,   2675.899,   9587.624,
  //                    -3671.810,   3611.960, -9086.531, -5333.617, -3284.205,
  //                    5676.141, -8293.472
  VLOAD_32(v2, 0x460f36ad, 0x45ab810c, 0xc4ce09ad, 0xc59cf316, 0x45dfd8be, 0xc5d5509c, 0xc5da05f8, 0x45273e62,
           0x4615ce7f, 0xc5657cf5, 0x4561bf5b, 0xc60dfa20, 0xc5a6acf0, 0xc54d4347, 0x45b16120, 0xc60195e3);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.xu.f.w v4, v2, v0.t");
  //                       0,       5488,          0,          0,          0, 0,
  //                       0,       2676,          0,          0,          0, 0,
  //                       0,          0,          0,          0
  VCMP_U16(3, v4, 0x0000, 0x1570, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0a74, 0x0000, 0x0000, 0x0000, 0x0000,
           0x0000, 0x0000, 0x0000, 0x0000);

  VSET(16, e8, m1);
  // 0.000000, 134.237000, 12.473999, 0.711000, 134.947998,
  // 13.184998, 1.422000, 135.658997, 13.895996, 2.133000,
  // 136.369995, 14.606995, 2.844000, 137.080994, 15.317993, 3.555000
  VLOAD_16(v2, 0x0000, 0x5832, 0x4a3d, 0x39b0, 0x5838, 0x4a98, 0x3db0, 0x583d, 0x4af3, 0x4044, 0x5843, 0x4b4e, 0x41b0,
           0x5849, 0x4ba9, 0x431c);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.xu.f.w v4, v2, v0.t");
  VCMP_U8(4, v4, 0x00, 0x86, 0x00, 0x01, 0x00, 0x0d, 0x00, 0x88, 0x00, 0x02, 0x00, 0x0f, 0x00, 0x89, 0x00, 0x04);
};

////////////////
// vfncvt.x.f //
////////////////

// Simple random test with similar values
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  //              -7808.056,   9317.408,   1685.891,   3975.596, -5978.108,
  //              9676.333,   6963.966,   3589.870, -4334.772, -3261.309,
  //              -2340.480,   6085.075,   4043.322,   2827.902,   4389.497,
  //              -5196.684
  VLOAD_32(v2, 0xc5f40072, 0x461195a2, 0x44d2bc86, 0x4578798a, 0xc5bad0dd, 0x46173155, 0x45d99fbb, 0x45605ded,
           0xc587762e, 0xc54bd4f0, 0xc51247af, 0x45be2899, 0x457cb528, 0x4530be6f, 0x45892bfa, 0xc5a26578);
  asm volatile("vfncvt.x.f.w v4, v2");
  //                   -7808,       9317,       1686,       3976,      -5978,
  //                   9676,       6964,       3590,      -4335,      -3261,
  //                   -2340,       6085,       4043,       2828,       4389,
  //                   -5197
  VCMP_U16(5, v4, 0xe180, 0x2465, 0x0696, 0x0f88, 0xe8a6, 0x25cc, 0x1b34, 0x0e06, 0xef11, 0xf343, 0xf6dc, 0x17c5,
           0x0fcb, 0x0b0c, 0x1125, 0xebb3);

  VSET(16, e8, m1);
  // -128.000000, 6.237000, -115.526001, -127.289001, 6.947998,
  // -114.815002, -126.578003, 7.658997, -114.104004, -125.866997,
  // 8.369995, -113.393005, -125.155998, 9.080994, -112.682007, -124.445000
  VLOAD_16(v2, 0xd800, 0x463d, 0xd738, 0xd7f5, 0x46f3, 0xd72d, 0xd7e9, 0x47a9, 0xd722, 0xd7de, 0x482f, 0xd716, 0xd7d2,
           0x488a, 0xd70b, 0xd7c7);
  asm volatile("vfncvt.x.f.w v4, v2");
  VCMP_U8(6, v4, 0x80, 0x06, 0x8c, 0x81, 0x07, 0x8d, 0x81, 0x08, 0x8e, 0x82, 0x08, 0x8f, 0x83, 0x09, 0x8f, 0x84);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  //              -7808.056,   9317.408,   1685.891,   3975.596, -5978.108,
  //              9676.333,   6963.966,   3589.870, -4334.772, -3261.309,
  //              -2340.480,   6085.075,   4043.322,   2827.902,   4389.497,
  //              -5196.684
  VLOAD_32(v2, 0xc5f40072, 0x461195a2, 0x44d2bc86, 0x4578798a, 0xc5bad0dd, 0x46173155, 0x45d99fbb, 0x45605ded,
           0xc587762e, 0xc54bd4f0, 0xc51247af, 0x45be2899, 0x457cb528, 0x4530be6f, 0x45892bfa, 0xc5a26578);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.x.f.w v4, v2, v0.t");
  //                       0,       9317,          0,       3976,          0,
  //                       9676,          0,       3590,          0,      -3261,
  //                       0,       6085,          0,       2828,          0,
  //                       -5197
  VCMP_U16(7, v4, 0x0000, 0x2465, 0x0000, 0x0f88, 0x0000, 0x25cc, 0x0000, 0x0e06, 0x0000, 0xf343, 0x0000, 0x17c5,
           0x0000, 0x0b0c, 0x0000, 0xebb3);

  VSET(16, e8, m1);
  // -128.000000, 6.237000, -115.526001, -127.289001, 6.947998,
  // -114.815002, -126.578003, 7.658997, -114.104004, -125.866997,
  // 8.369995, -113.393005, -125.155998, 9.080994, -112.682007, -124.445000
  VLOAD_16(v2, 0xd800, 0x463d, 0xd738, 0xd7f5, 0x46f3, 0xd72d, 0xd7e9, 0x47a9, 0xd722, 0xd7de, 0x482f, 0xd716, 0xd7d2,
           0x488a, 0xd70b, 0xd7c7);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.x.f.w v4, v2, v0.t");
  VCMP_U8(8, v4, 0x00, 0x06, 0x00, 0x81, 0x00, 0x8d, 0x00, 0x08, 0x00, 0x82, 0x00, 0x8f, 0x00, 0x09, 0x00, 0x84);
};

/////////////////////
// vfncvt.rtz.xu.f //
/////////////////////

// Simple random test with similar values
void TEST_CASE5(void) {
  VSET(16, e16, m1);
  //              -9750.252, -4363.736, -2345.615,   6996.062, -7115.004,
  //              6670.171, -4079.234, -1773.082,   254.350,   53.058,
  //              -9041.926, -8137.022,   1522.146,   198.516, -920.430,
  //              2857.583
  VLOAD_32(v2, 0xc6185902, 0xc5885de3, 0xc51299d6, 0x45daa07e, 0xc5de5808, 0x45d0715e, 0xc57ef3bf, 0xc4dda29c,
           0x437e5998, 0x42543afb, 0xc60d47b4, 0xc5fe482e, 0x44be44af, 0x43468433, 0xc4661b8b, 0x45329953);
  asm volatile("vfncvt.rtz.xu.f.w v4, v2");
  //                       0,          0,          0,       6996,          0,
  //                       6670,          0,          0,        254,         53,
  //                       0,          0,       1522,        198,          0,
  //                       2857
  VCMP_U16(9, v4, 0x0000, 0x0000, 0x0000, 0x1b54, 0x0000, 0x1a0e, 0x0000, 0x0000, 0x00fe, 0x0035, 0x0000, 0x0000,
           0x05f2, 0x00c6, 0x0000, 0x0b29);

  VSET(16, e8, m1);
  // 1.500000, 134.237000, 12.473999, 0.711000, 134.947998,
  // 13.184998, 1.422000, 135.658997, 13.895996, 2.133000,
  // 136.369995, 14.606995, 2.844000, 137.080994, 15.317993, 3.555000
  VLOAD_16(v2, 0x5832, 0x3e00, 0x4a3d, 0x39b0, 0x5838, 0x4a98, 0x3db0, 0x583d, 0x4af3, 0x4044, 0x5843, 0x4b4e, 0x41b0,
           0x5849, 0x4ba9, 0x431c);
  asm volatile("vfncvt.rtz.xu.f.w v4, v2");
  VCMP_U8(10, v4, 0x86, 0x01, 0x0c, 0x00, 0x87, 0x0d, 0x01, 0x87, 0x0d, 0x02, 0x88, 0x0e, 0x02, 0x89, 0x0f, 0x03);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE6(void) {
  VSET(16, e16, m1);
  //              -9750.252, -4363.736, -2345.615,   6996.062, -7115.004,
  //              6670.171, -4079.234, -1773.082,   254.350,   53.058,
  //              -9041.926, -8137.022,   1522.146,   198.516, -920.430,
  //              2857.583
  VLOAD_32(v2, 0xc6185902, 0xc5885de3, 0xc51299d6, 0x45daa07e, 0xc5de5808, 0x45d0715e, 0xc57ef3bf, 0xc4dda29c,
           0x437e5998, 0x42543afb, 0xc60d47b4, 0xc5fe482e, 0x44be44af, 0x43468433, 0xc4661b8b, 0x45329953);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.rtz.xu.f.w v4, v2, v0.t");
  //                       0,          0,          0,       6996,          0,
  //                       6670,          0,          0,          0,         53,
  //                       0,          0,          0,        198,          0,
  //                       2857
  VCMP_U16(11, v4, 0x0000, 0x0000, 0x0000, 0x1b54, 0x0000, 0x1a0e, 0x0000, 0x0000, 0x0000, 0x0035, 0x0000, 0x0000,
           0x0000, 0x00c6, 0x0000, 0x0b29);

  VSET(16, e8, m1);
  // 1.500000, 134.237000, 12.473999, 0.711000, 134.947998,
  // 13.184998, 1.422000, 135.658997, 13.895996, 2.133000,
  // 136.369995, 14.606995, 2.844000, 137.080994, 15.317993, 3.555000
  VLOAD_16(v2, 0x5832, 0x3e00, 0x4a3d, 0x39b0, 0x5838, 0x4a98, 0x3db0, 0x583d, 0x4af3, 0x4044, 0x5843, 0x4b4e, 0x41b0,
           0x5849, 0x4ba9, 0x431c);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.rtz.xu.f.w v4, v2, v0.t");
  VCMP_U8(12, v4, 0x00, 0x01, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x87, 0x00, 0x02, 0x00, 0x0e, 0x00, 0x89, 0x00, 0x03);
};

////////////////////
// vfncvt.rtz.x.f //
////////////////////

// Simple random test with similar values
void TEST_CASE7(void) {
  VSET(16, e16, m1);
  //                9352.418, -5719.459,   4617.815, -3012.009, -3597.063,
  //                -5717.140, -3327.545,   1286.004,   1797.767,   3842.966,
  //                -2148.369, -7283.256,   8783.331, -7958.880, -6728.271,
  //                4727.792
  VLOAD_32(v2, 0x461221ac, 0xc5b2bbac, 0x45904e86, 0xc53c4026, 0xc560d104, 0xc5b2a91e, 0xc54ff8b9, 0x44a0c01e,
           0x44e0b88c, 0x45702f76, 0xc50645e9, 0xc5e39a0c, 0x46093d53, 0xc5f8b70a, 0xc5d2422c, 0x4593be56);
  asm volatile("vfncvt.rtz.x.f.w v4, v2");
  //                    9352,      -5719,       4617,      -3012,      -3597,
  //                    -5717,      -3327,       1286,       1797,       3842,
  //                    -2148,      -7283,       8783,      -7958,      -6728,
  //                    4727
  VCMP_U16(13, v4, 0x2488, 0xe9a9, 0x1209, 0xf43c, 0xf1f3, 0xe9ab, 0xf301, 0x0506, 0x0705, 0x0f02, 0xf79c, 0xe38d,
           0x224f, 0xe0ea, 0xe5b8, 0x1277);

  VSET(16, e8, m1);
  // -128.000000, 6.237000, -115.526001, -127.289001, 6.947998,
  // -114.815002, -126.578003, 7.658997, -114.104004, -125.866997,
  // 8.369995, -113.393005, -125.155998, 9.080994, -112.682007, -124.445000
  VLOAD_16(v2, 0xd800, 0x463d, 0xd738, 0xd7f5, 0x46f3, 0xd72d, 0xd7e9, 0x47a9, 0xd722, 0xd7de, 0x482f, 0xd716, 0xd7d2,
           0x488a, 0xd70b, 0xd7c7);
  asm volatile("vfncvt.rtz.x.f.w v4, v2");
  VCMP_U8(14, v4, 0x80, 0x06, 0x8d, 0x81, 0x06, 0x8e, 0x82, 0x07, 0x8e, 0x83, 0x08, 0x8f, 0x83, 0x09, 0x90, 0x84);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE8(void) {
  VSET(16, e16, m1);
  //                9352.418, -5719.459,   4617.815, -3012.009, -3597.063,
  //                -5717.140, -3327.545,   1286.004,   1797.767,   3842.966,
  //                -2148.369, -7283.256,   8783.331, -7958.880, -6728.271,
  //                4727.792
  VLOAD_32(v2, 0x461221ac, 0xc5b2bbac, 0x45904e86, 0xc53c4026, 0xc560d104, 0xc5b2a91e, 0xc54ff8b9, 0x44a0c01e,
           0x44e0b88c, 0x45702f76, 0xc50645e9, 0xc5e39a0c, 0x46093d53, 0xc5f8b70a, 0xc5d2422c, 0x4593be56);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.rtz.x.f.w v4, v2, v0.t");
  //                       0,      -5719,          0,      -3012,          0,
  //                       -5717,          0,       1286,          0, 3842, 0,
  //                       -7283,          0,      -7958,          0,       4727
  VCMP_U16(15, v4, 0x0000, 0xe9a9, 0x0000, 0xf43c, 0x0000, 0xe9ab, 0x0000, 0x0506, 0x0000, 0x0f02, 0x0000, 0xe38d,
           0x0000, 0xe0ea, 0x0000, 0x1277);

  VSET(16, e8, m1);
  // -128.000000, 6.237000, -115.526001, -127.289001, 6.947998,
  // -114.815002, -126.578003, 7.658997, -114.104004, -125.866997,
  // 8.369995, -113.393005, -125.155998, 9.080994, -112.682007, -124.445000
  VLOAD_16(v2, 0xd800, 0x463d, 0xd738, 0xd7f5, 0x46f3, 0xd72d, 0xd7e9, 0x47a9, 0xd722, 0xd7de, 0x482f, 0xd716, 0xd7d2,
           0x488a, 0xd70b, 0xd7c7);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.rtz.x.f.w v4, v2, v0.t");
  VCMP_U8(16, v4, 0x00, 0x06, 0x00, 0x81, 0x00, 0x8e, 0x00, 0x07, 0x00, 0x83, 0x00, 0x8f, 0x00, 0x09, 0x00, 0x84);
};

/////////////////
// vfncvt.f.xu //
/////////////////

// Simple random test with similar values
void TEST_CASE9(void) {
  VSET(16, e16, m1);
  //                 4294964178,       5853,    4294962638,    4294962082, 4585,
  //                 1637,       3984,    4294964217,       9553,    4294962615,
  //                 4294962166,       9867,    4294958580,    4294966752, 5172,
  //                 7478
  VLOAD_32(v2, 0xfffff3d2, 0x000016dd, 0xffffedce, 0xffffeba2, 0x000011e9, 0x00000665, 0x00000f90, 0xfffff3f9,
           0x00002551, 0xffffedb7, 0xffffebf6, 0x0000268b, 0xffffddf4, 0xfffffde0, 0x00001434, 0x00001d36);
  asm volatile("vfncvt.f.xu.w v4, v2");
  //                     inf,   5852.000,   inf,   inf,   4584.000,   1637.000,
  //                     3984.000,   inf,   9552.000,   inf,   inf,   9864.000,
  //                     inf,   inf,   5172.000,   7480.000
  VCMP_U16(17, v4, 0x7c00, 0x6db7, 0x7c00, 0x7c00, 0x6c7a, 0x6665, 0x6bc8, 0x7c00, 0x70aa, 0x7c00, 0x7c00, 0x70d1,
           0x7c00, 0x7c00, 0x6d0d, 0x6f4e);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE10(void) {
  VSET(16, e16, m1);
  //                 4294964178,       5853,    4294962638,    4294962082, 4585,
  //                 1637,       3984,    4294964217,       9553,    4294962615,
  //                 4294962166,       9867,    4294958580,    4294966752, 5172,
  //                 7478
  VLOAD_32(v2, 0xfffff3d2, 0x000016dd, 0xffffedce, 0xffffeba2, 0x000011e9, 0x00000665, 0x00000f90, 0xfffff3f9,
           0x00002551, 0xffffedb7, 0xffffebf6, 0x0000268b, 0xffffddf4, 0xfffffde0, 0x00001434, 0x00001d36);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.f.xu.w v4, v2, v0.t");
  //                0.000,   5852.000,   0.000,   inf,   0.000,   1637.000,
  //                0.000,   inf,   0.000,   inf,   0.000,   9864.000,   0.000,
  //                inf,   0.000,   7480.000
  VCMP_U16(19, v4, 0x0, 0x6db7, 0x0, 0x7c00, 0x0, 0x6665, 0x0, 0x7c00, 0x0, 0x7c00, 0x0, 0x70d1, 0x0, 0x7c00, 0x0,
           0x6f4e);
};

////////////////
// vfncvt.f.x //
////////////////

// Simple random test with similar values
void TEST_CASE11(void) {
  VSET(16, e16, m1);
  //                       -6279,           3717,           9022, -8925, -5530,
  //                       3851,       5592,      -3692,      -2747,       -748,
  //                       -2621,      -9352,       4018,       3174, -6975,
  //                       -4466
  VLOAD_32(v2, 0xffffe779, 0x00000e85, 0x0000233e, 0xffffdd23, 0xffffea66, 0x00000f0b, 0x000015d8, 0xfffff194,
           0xfffff545, 0xfffffd14, 0xfffff5c3, 0xffffdb78, 0x00000fb2, 0x00000c66, 0xffffe4c1, 0xffffee8e);
  asm volatile("vfncvt.f.x.w v4, v2");
  //                -6280.000,   3716.000,   9024.000,  -8928.000,  -5528.000,
  //                3852.000,   5592.000, -3692.000, -2748.000, -748.000,
  //                -2620.000, -9352.000,   4018.000,   3174.000, -6976.000,
  //                -4464.000
  VCMP_U16(21, v4, 0xee22, 0x6b42, 0x7068, 0xf05c, 0xed66, 0x6b86, 0x6d76, 0xeb36, 0xe95e, 0xe1d8, 0xe91e, 0xf091,
           0x6bd9, 0x6a33, 0xeed0, 0xec5c);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE12(void) {
  VSET(16, e16, m1);
  //                   -6279,       3717,       9022,      -8925,      -5530,
  //                   3851,       5592,      -3692,      -2747,       -748,
  //                   -2621,      -9352,       4018,       3174,      -6975,
  //                   -4466
  VLOAD_32(v2, 0xffffe779, 0x00000e85, 0x0000233e, 0xffffdd23, 0xffffea66, 0x00000f0b, 0x000015d8, 0xfffff194,
           0xfffff545, 0xfffffd14, 0xfffff5c3, 0xffffdb78, 0x00000fb2, 0x00000c66, 0xffffe4c1, 0xffffee8e);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.f.x.w v4, v2, v0.t");
  //                0.000,   3716.000,   0.000, -8928.000,   0.000,   3852.000,
  //                0.000, -3692.000,   0.000, -748.000,   0.000, -9352.000,
  //                0.000,   3174.000,   0.000, -4464.000
  VCMP_U16(23, v4, 0x0, 0x6b42, 0x0, 0xf05c, 0x0, 0x6b86, 0x0, 0xeb36, 0x0, 0xe1d8, 0x0, 0xf091, 0x0, 0x6a33, 0x0,
           0xec5c);
};

////////////////
// vfncvt.f.f //
////////////////

// Simple random test with similar values
void TEST_CASE13(void) {
  VSET(16, e16, m1);
  //              908.994, -6788.630, -5789.335, 8054.104, 3947.551, 9596.856,
  //              2474.506, 3094.286, 7684.992, -6850.149, -54.922, 7737.443,
  //              4171.873, 5266.611, 9163.839, 5679.187
  VLOAD_32(v2, 0x44633fa3, 0xc5d4250b, 0xc5b4eaaf, 0x45fbb0d4, 0x4576b8d0, 0x4615f36d, 0x451aa818, 0x45416494,
           0x45f027ef, 0xc5d61131, 0xc25bb026, 0x45f1cb8c, 0x45825efb, 0x45a494e4, 0x460f2f5b, 0x45b1797f);
  asm volatile("vfncvt.f.f.w v4, v2");
  //              909.000, -6788.000, -5788.000, 8056.000, 3948.000, 9600.000,
  //              2474.000, 3094.000, 7684.000, -6852.000, -54.938, 7736.000,
  //              4172.000, 5268.000, 9160.000, 5680.000
  VCMP_U16(25, v4, 0x631a, 0xeea1, 0xeda7, 0x6fde, 0x6bb6, 0x70b0, 0x68d5, 0x6a0b, 0x6f81, 0xeeb1, 0xd2de, 0x6f8e,
           0x6c13, 0x6d25, 0x7079, 0x6d8c);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE14(void) {
  VSET(16, e16, m1);
  //              908.994, -6788.630, -5789.335, 8054.104, 3947.551, 9596.856,
  //              2474.506, 3094.286, 7684.992, -6850.149, -54.922, 7737.443,
  //              4171.873, 5266.611, 9163.839, 5679.187
  VLOAD_32(v2, 0x44633fa3, 0xc5d4250b, 0xc5b4eaaf, 0x45fbb0d4, 0x4576b8d0, 0x4615f36d, 0x451aa818, 0x45416494,
           0x45f027ef, 0xc5d61131, 0xc25bb026, 0x45f1cb8c, 0x45825efb, 0x45a494e4, 0x460f2f5b, 0x45b1797f);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.f.f.w v4, v2, v0.t");
  //              0.000, -6788.000, 0.000, 8056.000, 0.000, 9600.000, 0.000,
  //              3094.000, 0.000, -6852.000, 0.000, 7736.000, 0.000, 5268.000,
  //              0.000, 5680.000
  VCMP_U16(27, v4, 0x0, 0xeea1, 0x0, 0x6fde, 0x0, 0x70b0, 0x0, 0x6a0b, 0x0, 0xeeb1, 0x0, 0x6f8e, 0x0, 0x6d25, 0x0,
           0x6d8c);
};

////////////////////
// vfncvt.rod.f.f //
////////////////////

// Simple random test with similar values
void TEST_CASE15(void) {
  VSET(16, e16, m1);
  //                     908.994, -6788.630, -5789.335, 8054.104, 3947.551,
  //                     9596.856, 2474.506, 3094.286, 7684.992, -6850.149,
  //                     -54.922, 7737.443, 4171.873, 5266.611, 9163.839,
  //                     5679.187
  VLOAD_32(v2, 0x44633fa3, 0xc5d4250b, 0xc5b4eaaf, 0x45fbb0d4, 0x4576b8d0, 0x4615f36d, 0x451aa818, 0x45416494,
           0x45f027ef, 0xc5d61131, 0xc25bb026, 0x45f1cb8c, 0x45825efb, 0x45a494e4, 0x460f2f5b, 0x45b1797f);
  asm volatile("vfncvt.rod.f.f.w v4, v2");
  //                  909.000, -6788.000, -5788.000, 8056.000, 3948.000,
  //                  9600.000, 2474.000, 3094.000, 7684.000, -6852.000,
  //                  -54.938, 7736.000, 4172.000, 5268.000, 9160.000, 5680.000
  VCMP_U16(29, v4, 0x6319, 0xeea1, 0xeda7, 0x6fdd, 0x6bb5, 0x70af, 0x68d5, 0x6a0b, 0x6f81, 0xeeb1, 0xd2dd, 0x6f8f,
           0x6c13, 0x6d25, 0x7079, 0x6d8b);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE16(void) {
  VSET(16, e16, m1);
  //              908.994, -6788.630, -5789.335, 8054.104, 3947.551, 9596.856,
  //              2474.506, 3094.286, 7684.992, -6850.149, -54.922, 7737.443,
  //              4171.873, 5266.611, 9163.839, 5679.187
  VLOAD_32(v2, 0x44633fa3, 0xc5d4250b, 0xc5b4eaaf, 0x45fbb0d4, 0x4576b8d0, 0x4615f36d, 0x451aa818, 0x45416494,
           0x45f027ef, 0xc5d61131, 0xc25bb026, 0x45f1cb8c, 0x45825efb, 0x45a494e4, 0x460f2f5b, 0x45b1797f);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfncvt.rod.f.f.w v4, v2, v0.t");
  //              0.000, -6788.000, 0.000, 8056.000, 0.000, 9600.000, 0.000,
  //              3094.000, 0.000, -6852.000, 0.000, 7736.000, 0.000, 5268.000,
  //              0.000, 5680.000
  VCMP_U16(31, v4, 0x0, 0xeea1, 0x0, 0x6fdd, 0x0, 0x70af, 0x0, 0x6a0b, 0x0, 0xeeb1, 0x0, 0x6f8f, 0x0, 0x6d25, 0x0,
           0x6d8b);
};

int main(void) {
  enable_vec();
  enable_fp();

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());

  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  TEST_CASE5();
  MASKED_TEST(TEST_CASE6());

  TEST_CASE7();
  MASKED_TEST(TEST_CASE8());

  TEST_CASE9();
  MASKED_TEST(TEST_CASE10());

  TEST_CASE11();
  MASKED_TEST(TEST_CASE12());

  TEST_CASE13();
  MASKED_TEST(TEST_CASE14());

  /*
  vfncvt.rod.f.f is not supported yet

  //  TEST_CASE15();
  //  TEST_CASE16();
  */

  EXIT_CHECK();
}
