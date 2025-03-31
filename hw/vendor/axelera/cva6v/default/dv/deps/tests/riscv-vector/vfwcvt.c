// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matteo Perotti <mperotti@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

// We assume RNE rounding when not specified by the encoding

/////////////////
// vfwcvt.xu.f //
/////////////////

void TEST_CASE1(void) {
  VSET(16, e16, m1);
  //                 56.438,    -30.938,    -68.438,    -32.969,     56.438,
  //                 -5.816,   53.094, -29.875, -93.562, -90.750, -65.875,
  //                 -91.062,   16.281, -77.938, -67.000, -51.844
  VLOAD_16(v2, 0x530e, 0xcfbc, 0xd447, 0xd01f, 0x530e, 0xc5d1, 0x52a3, 0xcf78, 0xd5d9, 0xd5ac, 0xd41e, 0xd5b1, 0x4c12,
           0xd4df, 0xd430, 0xd27b);
  asm volatile("vfwcvt.xu.f.v v4, v2");
  VSET(16, e32, m2);
  //                           56,              0,              0, 0, 56, 0, 53,
  //                           0,              0,              0, 0, 0, 16, 0,
  //                           0,              0
  VCMP_U32(1, v4, 0x00000038, 0x00000000, 0x00000000, 0x00000000, 0x00000038, 0x00000000, 0x00000035, 0x00000000,
           0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000010, 0x00000000, 0x00000000, 0x00000000);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //                 -36.375,    56.438, -68.438, -32.969,   56.438,
  //                 -5.816,   53.094, -29.875, -93.562, -90.750, -65.875,
  //                 -91.062,   16.281, -77.938, -67.000, -51.844
  VLOAD_16(v2, 0xd08c, 0x530e, 0xd447, 0xd01f, 0x530e, 0xc5d1, 0x52a3, 0xcf78, 0xd5d9, 0xd5ac, 0xd41e, 0xd5b1, 0x4c12,
           0xd4df, 0xd430, 0xd27b);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.xu.f.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                           0,             56,              0, 0, 0, 0, 0, 0,
  //                           0,              0,              0, 0, 0, 0, 0, 0
  VCMP_U32(3, v4, 0x00000000, 0x00000038, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
           0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000);
};

////////////////
// vfwcvt.x.f //
////////////////

// Simple random test with similar values
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  //                 -55.656,    -23.391,     53.094, -0.356,   26.859, -81.938,
  //                 63.625, -54.594, -36.375,   77.312,   73.188, -79.500,
  //                 -22.047, -30.500,   33.375, -26.281
  VLOAD_16(v2, 0xd2f5, 0xcdd9, 0x52a3, 0xb5b2, 0x4eb7, 0xd51f, 0x53f4, 0xd2d3, 0xd08c, 0x54d5, 0x5493, 0xd4f8, 0xcd83,
           0xcfa0, 0x502c, 0xce92);
  asm volatile("vfwcvt.x.f.v v4, v2");
  VSET(16, e32, m2);
  //                         -56,            -23,             53, 0, 27, -82,
  //                         64,            -55,            -36,             77,
  //                         73,            -80,            -22,            -30,
  //                         33,            -26
  VCMP_U32(5, v4, 0xffffffc8, 0xffffffe9, 0x00000035, 0x00000000, 0x0000001b, 0xffffffae, 0x00000040, 0xffffffc9,
           0xffffffdc, 0x0000004d, 0x00000049, 0xffffffb0, 0xffffffea, 0xffffffe2, 0x00000021, 0xffffffe6);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  //                 -55.656,    -23.391,   53.094, -0.356,   26.859,
  //                 -81.938,   63.625, -54.594, -36.375,   77.312,   73.188,
  //                 -79.500, -22.047, -30.500,   33.375, -26.281
  VLOAD_16(v2, 0xd2f5, 0xcdd9, 0x52a3, 0xb5b2, 0x4eb7, 0xd51f, 0x53f4, 0xd2d3, 0xd08c, 0x54d5, 0x5493, 0xd4f8, 0xcd83,
           0xcfa0, 0x502c, 0xce92);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.x.f.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                           0,            -23,              0, 0, 0, -82, 0,
  //                           -55,              0,             77, 0, -80, 0,
  //                           -30,              0,            -26
  VCMP_U32(7, v4, 0x00000000, 0xffffffe9, 0x00000000, 0x00000000, 0x00000000, 0xffffffae, 0x00000000, 0xffffffc9,
           0x00000000, 0x0000004d, 0x00000000, 0xffffffb0, 0x00000000, 0xffffffe2, 0x00000000, 0xffffffe6);
};

/////////////////////
// vfwcvt.rtz.xu.f //
/////////////////////

// Simple random test with similar values
void TEST_CASE5(void) {
  VSET(16, e16, m1);
  //                26304.000, -31056.000,   6932.000,   63168.000, -10920.000,
  //                -38528.000,   inf, -inf, -1313.000,   52736.000,   inf,
  //                -inf, -61024.000, -inf, -5672.000,   53824.000
  VLOAD_16(v2, 0x766c, 0xf795, 0x6ec5, 0x7bb6, 0xf155, 0xf8b4, 0x7c00, 0xfc00, 0xe521, 0x7a70, 0x7c00, 0xfc00, 0xfb73,
           0xfc00, 0xed8a, 0x7a92);
  asm volatile("vfwcvt.rtz.xu.f.v v4, v2");
  VSET(16, e32, m2);
  //                       26304,              0,           6932, 63168, 0, 0,
  //                       0,              0,              0,          52736, 0,
  //                       0,              0,              0,              0,
  //                       53824
  VCMP_U32(9, v4, 0x000066c0, 0x00000000, 0x00001b14, 0x0000f6c0, 0x00000000, 0x00000000, 0xffffffff, 0x00000000,
           0x00000000, 0x0000ce00, 0xffffffff, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x0000d240);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE6(void) {
  VSET(16, e16, m1);
  //                26304.000, -31056.000,   6932.000,   63168.000, -10920.000,
  //                -38528.000,   inf, -inf, -1313.000,   52736.000,   inf,
  //                -inf, -61024.000, -inf, -5672.000,   53824.000
  VLOAD_16(v2, 0x766c, 0xf795, 0x6ec5, 0x7bb6, 0xf155, 0xf8b4, 0x7c00, 0xfc00, 0xe521, 0x7a70, 0x7c00, 0xfc00, 0xfb73,
           0xfc00, 0xed8a, 0x7a92);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.rtz.xu.f.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                           0,              0,              0, 63168, 0, 0,
  //                           0,              0,              0, 52736, 0, 0,
  //                           0,              0,              0,          53824
  VCMP_U32(11, v4, 0x00000000, 0x00000000, 0x00000000, 0x0000f6c0, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
           0x00000000, 0x0000ce00, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x0000d240);
};

////////////////////
// vfwcvt.rtz.x.f //
////////////////////

// Simple random test with similar values
void TEST_CASE7(void) {
  VSET(16, e16, m1);
  //                5.844,   36.219, -86.250,   20.406, -45.688,   13.961,
  //                -96.562,   81.000, -32.594,   51.281,   80.750,
  //                -17.750,   14.516,   58.000,   69.938, -94.688
  VLOAD_16(v2, 0x45d8, 0x5087, 0xd564, 0x4d1a, 0xd1b6, 0x4afb, 0xd609, 0x5510, 0xd013, 0x5269, 0x550c, 0xcc70, 0x4b42,
           0x5340, 0x545f, 0xd5eb);
  asm volatile("vfwcvt.rtz.x.f.v v4, v2");
  VSET(16, e32, m2);
  //                           5,             36,            -86, 20, -45, 13,
  //                           -96,             81,            -32, 51, 80, -17,
  //                           14,             58,             69, -94
  VCMP_U32(13, v4, 0x00000005, 0x00000024, 0xffffffaa, 0x00000014, 0xffffffd3, 0x0000000d, 0xffffffa0, 0x00000051,
           0xffffffe0, 0x00000033, 0x00000050, 0xffffffef, 0x0000000e, 0x0000003a, 0x00000045, 0xffffffa2);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE8(void) {
  VSET(16, e16, m1);
  //                5.844,   36.219, -86.250,   20.406, -45.688,   13.961,
  //                -96.562,   81.000, -32.594,   51.281,   80.750,
  //                -17.750,   14.516,   58.000,   69.938, -94.688
  VLOAD_16(v2, 0x45d8, 0x5087, 0xd564, 0x4d1a, 0xd1b6, 0x4afb, 0xd609, 0x5510, 0xd013, 0x5269, 0x550c, 0xcc70, 0x4b42,
           0x5340, 0x545f, 0xd5eb);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.rtz.x.f.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                           0,             36,              0, 20, 0, 13, 0,
  //                           81,              0,             51, 0, -17, 0,
  //                           58,              0,            -94
  VCMP_U32(15, v4, 0x00000000, 0x00000024, 0x00000000, 0x00000014, 0x00000000, 0x0000000d, 0x00000000, 0x00000051,
           0x00000000, 0x00000033, 0x00000000, 0xffffffef, 0x00000000, 0x0000003a, 0x00000000, 0xffffffa2);
};

/////////////////
// vfwcvt.f.xu //
/////////////////

// Simple random test with similar values
void TEST_CASE9(void) {
  VSET(16, e16, m1);
  //                    64656,       64687,       64823,         970, 543,
  //                    65038,       65122,         966,         180, 389, 337,
  //                    341,       65240,          51,       64922,       64676
  VLOAD_16(v2, 0xfc90, 0xfcaf, 0xfd37, 0x03ca, 0x021f, 0xfe0e, 0xfe62, 0x03c6, 0x00b4, 0x0185, 0x0151, 0x0155, 0xfed8,
           0x0033, 0xfd9a, 0xfca4);
  asm volatile("vfwcvt.f.xu.v v4, v2");
  VSET(16, e32, m2);
  //                   64656.000,      64687.000,      64823.000,      970.000,
  //                   543.000,      65038.000,      65122.000,      966.000,
  //                   180.000,      389.000,      337.000,      341.000,
  //                   65240.000,      51.000,      64922.000,      64676.000
  VCMP_U32(17, v4, 0x477c9000, 0x477caf00, 0x477d3700, 0x44728000, 0x4407c000, 0x477e0e00, 0x477e6200, 0x44718000,
           0x43340000, 0x43c28000, 0x43a88000, 0x43aa8000, 0x477ed800, 0x424c0000, 0x477d9a00, 0x477ca400);

  VSET(16, e8, m1);
  //                    252,      175,       55,       202, 31,
  //                    14,       98,        198,      180, 133, 81,
  //                    85,       216,       51,       154,      164
  VLOAD_8(v2, 0xfc, 0xaf, 0x37, 0xca, 0x1f, 0x0e, 0x62, 0xc6, 0xb4, 0x85, 0x51, 0x55, 0xd8, 0x33, 0x9a, 0xa4);
  asm volatile("vfwcvt.f.xu.v v4, v2");
  VSET(16, e16, m1);
  //                   252.000,      175.000,      55.000,      202.000,
  //                   31.000,       14.000,       98.000,      198.000,
  //                   180.000,      133.000,      81.000,      85.000,
  //                   216.000,      51.000,       154.000,     164.000
  VCMP_U16(18, v4, 0x5be0, 0x5978, 0x52e0, 0x5a50, 0x4fc0, 0x4b00, 0x5620, 0x5a30, 0x59a0, 0x5828, 0x5510, 0x5550,
           0x5ac0, 0x5260, 0x58d0, 0x5920);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE10(void) {
  VSET(16, e16, m1);
  //                    64656,       64687,       64823,         970, 543,
  //                    65038,       65122,         966,         180, 389, 337,
  //                    341,       65240,          51,       64922,       64676
  VLOAD_16(v2, 0xfc90, 0xfcaf, 0xfd37, 0x03ca, 0x021f, 0xfe0e, 0xfe62, 0x03c6, 0x00b4, 0x0185, 0x0151, 0x0155, 0xfed8,
           0x0033, 0xfd9a, 0xfca4);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.f.xu.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                   0.000,      64687.000,      0.000,      970.000, 0.000,
  //                   65038.000,      0.000,      966.000,      0.000, 389.000,
  //                   0.000,      341.000,      0.000,      51.000,      0.000,
  //                   64676.000
  VCMP_U32(19, v4, 0x0, 0x477caf00, 0x0, 0x44728000, 0x0, 0x477e0e00, 0x0, 0x44718000, 0x0, 0x43c28000, 0x0, 0x43aa8000,
           0x0, 0x424c0000, 0x0, 0x477ca400);

  VSET(16, e8, m1);
  //                    252,      175,       55,       202, 31,
  //                    14,       98,        198,      180, 133, 81,
  //                    85,       216,       51,       154,      164
  VLOAD_8(v2, 0xfc, 0xaf, 0x37, 0xca, 0x1f, 0x0e, 0x62, 0xc6, 0xb4, 0x85, 0x51, 0x55, 0xd8, 0x33, 0x9a, 0xa4);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfwcvt.f.xu.v v4, v2, v0.t");
  VSET(16, e16, m1);
  //                   0.000,        175.000,      0.000,       202.000,
  //                   0.000,        14.000,       0.000,       198.000,
  //                   0.000,        133.000,      0.000,       85.000,
  //                   0.000,        51.000,       0.000,       164.000
  VCMP_U16(20, v4, 0x0000, 0x5978, 0x0000, 0x5a50, 0x0000, 0x4b00, 0x0000, 0x5a30, 0x0000, 0x5828, 0x0000, 0x5550,
           0x0000, 0x5260, 0x0000, 0x5920);
};

////////////////
// vfwcvt.f.x //
////////////////

// Simple random test with similar values
void TEST_CASE11(void) {
  VSET(16, e16, m1);
  //                     -263,        -943,         111,        -140, -792,
  //                     -320,        -384,         250,        -308, 578, -830,
  //                     -865,         908,         264,          93, 833
  VLOAD_16(v2, 0xfef9, 0xfc51, 0x006f, 0xff74, 0xfce8, 0xfec0, 0xfe80, 0x00fa, 0xfecc, 0x0242, 0xfcc2, 0xfc9f, 0x038c,
           0x0108, 0x005d, 0x0341);
  asm volatile("vfwcvt.f.x.v v4, v2");
  VSET(16, e32, m2);
  //                  -263.000,     -943.000,      111.000,     -140.000,
  //                  -792.000,     -320.000,     -384.000,      250.000,
  //                  -308.000,      578.000,     -830.000,     -865.000,
  //                  908.000,      264.000,      93.000,      833.000
  VCMP_U32(21, v4, 0xc3838000, 0xc46bc000, 0x42de0000, 0xc30c0000, 0xc4460000, 0xc3a00000, 0xc3c00000, 0x437a0000,
           0xc39a0000, 0x44108000, 0xc44f8000, 0xc4584000, 0x44630000, 0x43840000, 0x42ba0000, 0x44504000);

  VSET(16, e8, m1);
  //                    -4,      -81,         55,      -54,   31,
  //                    14,       98,        -58,      -76,  -123,  81,
  //                    85,      -40,         51,      -102,       -92
  VLOAD_8(v2, 0xfc, 0xaf, 0x37, 0xca, 0x1f, 0x0e, 0x62, 0xc6, 0xb4, 0x85, 0x51, 0x55, 0xd8, 0x33, 0x9a, 0xa4);
  asm volatile("vfwcvt.f.x.v v4, v2");
  VSET(16, e16, m1);
  //                    -4.000,    -81.000,     55.000,    -54.000,   31.000,
  //                    14.000,     98.000,    -58.000,    -76.000,  -123.000,  81.000,
  //                    85.000,    -40.000,     51.000,    -102.000,           -92.000
  VCMP_U16(18, v4, 0xc400, 0xd510, 0x52e0, 0xd2c0, 0x4fc0, 0x4b00, 0x5620, 0xd340, 0xd4c0, 0xd7b0, 0x5510, 0x5550,
           0xd100, 0x5260, 0xd660, 0xd5c0);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE12(void) {
  VSET(16, e16, m1);
  //                     -263,        -943,         111,        -140, -792,
  //                     -320,        -384,         250,        -308, 578, -830,
  //                     -865,         908,         264,          93, 833
  VLOAD_16(v2, 0xfef9, 0xfc51, 0x006f, 0xff74, 0xfce8, 0xfec0, 0xfe80, 0x00fa, 0xfecc, 0x0242, 0xfcc2, 0xfc9f, 0x038c,
           0x0108, 0x005d, 0x0341);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.f.x.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                   0.000,     -943.000,      0.000,     -140.000, 0.000,
  //                   -320.000,      0.000,      250.000,      0.000, 578.000,
  //                   0.000,     -865.000,      0.000,      264.000, 0.000,
  //                   833.000
  VCMP_U32(23, v4, 0x0, 0xc46bc000, 0x0, 0xc30c0000, 0x0, 0xc3a00000, 0x0, 0x437a0000, 0x0, 0x44108000, 0x0, 0xc4584000,
           0x0, 0x43840000, 0x0, 0x44504000);

  VSET(16, e8, m1);
  //                    -4,      -81,         55,      -54,   31,
  //                    14,       98,        -58,      -76,  -123,  81,
  //                    85,      -40,         51,      -102,       -92
  VLOAD_8(v2, 0xfc, 0xaf, 0x37, 0xca, 0x1f, 0x0e, 0x62, 0xc6, 0xb4, 0x85, 0x51, 0x55, 0xd8, 0x33, 0x9a, 0xa4);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfwcvt.f.x.v v4, v2, v0.t");
  VSET(16, e16, m1);
  //                    -4.000,    -81.000,     55.000,    -54.000,   31.000,
  //                    14.000,     98.000,    -58.000,    -76.000,  -123.000,  81.000,
  //                    85.000,    -40.000,     51.000,    -102.000,           -92.000
  VCMP_U16(24, v4, 0x0000, 0xd510, 0x0000, 0xd2c0, 0x0000, 0x4b00, 0x0000, 0xd340, 0x0000, 0xd7b0, 0x0000, 0x5550,
           0x0000, 0x5260, 0x0000, 0xd5c0);
};

////////////////
// vfwcvt.f.f //
////////////////

// Simple random test with similar values
void TEST_CASE13(void) {
  VSET(16, e16, m1);
  //                83.312, -83.188,   62.469,   94.812,   10.797, -13.070,
  //                -9.039,   54.250, -92.188,   63.688, -32.875, -81.688,
  //                -62.219, -78.250, -29.703, -1.137
  VLOAD_16(v2, 0x5535, 0xd533, 0x53cf, 0x55ed, 0x4966, 0xca89, 0xc885, 0x52c8, 0xd5c3, 0x53f6, 0xd01c, 0xd51b, 0xd3c7,
           0xd4e4, 0xcf6d, 0xbc8c);
  asm volatile("vfwcvt.f.f.v v4, v2");
  VSET(16, e32, m2);
  //                83.312, -83.188,   62.469,   94.812,   10.797, -13.070,
  //                -9.039,   54.250, -92.188,   63.688, -32.875, -81.688,
  //                -62.219, -78.250, -29.703, -1.137
  VCMP_U32(25, v4, 0x42a6a000, 0xc2a66000, 0x4279e000, 0x42bda000, 0x412cc000, 0xc1512000, 0xc110a000, 0x42590000,
           0xc2b86000, 0x427ec000, 0xc2038000, 0xc2a36000, 0xc278e000, 0xc29c8000, 0xc1eda000, 0xbf918000);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE14(void) {
  VSET(16, e16, m1);
  //                83.312, -83.188,   62.469,   94.812,   10.797, -13.070,
  //                -9.039,   54.250, -92.188,   63.688, -32.875, -81.688,
  //                -62.219, -78.250, -29.703, -1.137
  VLOAD_16(v2, 0x5535, 0xd533, 0x53cf, 0x55ed, 0x4966, 0xca89, 0xc885, 0x52c8, 0xd5c3, 0x53f6, 0xd01c, 0xd51b, 0xd3c7,
           0xd4e4, 0xcf6d, 0xbc8c);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwcvt.f.f.v v4, v2, v0.t");
  VSET(16, e32, m2);
  //                0.000, -83.188,   0.000,   94.812,   0.000, -13.070, 0.000,
  //                54.250,   0.000,   63.688,   0.000, -81.688,   0.000,
  //                -78.250,   0.000, -1.137
  VCMP_U32(27, v4, 0x0, 0xc2a66000, 0x0, 0x42bda000, 0x0, 0xc1512000, 0x0, 0x42590000, 0x0, 0x427ec000, 0x0, 0xc2a36000,
           0x0, 0xc29c8000, 0x0, 0xbf918000);
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

  EXIT_CHECK();
}
