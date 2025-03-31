// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matteo Perotti <mperotti@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

// Simple random test with similar values + 1 subnormal
void TEST_CASE1(void) {
  VSET(16, e16, m1);
  //              -0.8057, -0.8564,  0.3425, -0.3066, -0.7314, -0.6396,  0.7588,
  //              -0.3743,  0.8706, -0.3064,  0.0390,  0.6123,  0.0237, -0.6201,
  //              -0.4524,  0.3337
  VLOAD_16(v2, 0xba72, 0xbada, 0x357b, 0xb4e8, 0xb9da, 0xb91e, 0x3a12, 0xb5fd, 0x3af7, 0xb4e7, 0x28fe, 0x38e6, 0x2612,
           0xb8f6, 0xb73d, 0x3557);
  //              -0.4094,  0.0410, -0.7305,  0.9038, -0.3545,  0.2830, -0.7051,
  //              -0.7124, -0.6348,  0.1256,  0.5576,  0.1334,  0.8779, -0.4836,
  //              0.3215,  0.4167
  VLOAD_16(v3, 0xb68d, 0x293e, 0xb9d8, 0x3b3b, 0xb5ac, 0x3487, 0xb9a4, 0xb9b3, 0xb914, 0x3005, 0x3876, 0x3045, 0x3b06,
           0xb7bd, 0x3525, 0x36ab);
  asm volatile("vfdiv.vv v1, v2, v3");
  //               1.9678, -20.9062, -0.4690, -0.3394,  2.0625, -2.2598,
  //               -1.0762,  0.5254, -1.3711, -2.4395,  0.0699,  4.5898, 0.0270,
  //               1.2822, -1.4072,  0.8008
  VCMP_U16(1, v1, 0x3fdf, 0xcd3a, 0xb780, 0xb56d, 0x4020, 0xc085, 0xbc4e, 0x3833, 0xbd7c, 0xc0e0, 0x2c79, 0x4496,
           0x26ea, 0x3d20, 0xbda0, 0x3a68);

  VSET(16, e32, m2);
  //               0.64838839,  0.00666664, -0.13619921,  0.21094505,
  //               -0.51040554, -0.77216595,  0.42111391,  0.82974166,
  //               -0.31227046,  0.68854737, -0.72970057,  0.10843290,
  //               -0.38442346,  0.18102080,  0.57249051,  0.76465768
  VLOAD_32(v4, 0x3f25fcc8, 0x3bda73da, 0xbe0b77ce, 0x3e5801fb, 0xbf02a9f0, 0xbf45acab, 0x3ed79c3e, 0x3f5469f3,
           0xbe9fe1ea, 0x3f3044a4, 0xbf3acda8, 0x3dde1212, 0xbec4d327, 0x3e395d84, 0x3f128ebd, 0x3f43c09b);
  //              -0.59629226, -0.46890569,  0.99662799, -0.49397555,
  //              0.80701596,  0.55786854, -0.26524273, -0.04642257,
  //              -0.67671824,  0.64403933,  0.06642481,  0.26544699,
  //              -0.00225505,  0.27478188,  0.76509053,  0.36194146
  VLOAD_32(v6, 0xbf18a69c, 0xbef01468, 0x3f7f2303, 0xbefcea5d, 0x3f4e9899, 0x3f0ed079, 0xbe87cde5, 0xbd3e2597,
           0xbf2d3d68, 0x3f24dfc3, 0x3d8809bb, 0x3e87e8ab, 0xbb13c97d, 0x3e8cb036, 0x3f43dcf9, 0x3eb95064);
  asm volatile("vfdiv.vv v2, v4, v6");
  //              -1.08736682, -0.01421745, -0.13666002, -0.42703542,
  //              -0.63246030, -1.38413608, -1.58765483, -17.87367058,
  //              0.46144828,  1.06910765, -10.98536205,  0.40849173,
  //              170.47213745,  0.65877998,  0.74826509,  2.11265564
  VCMP_U32(2, v2, 0xbf8b2ed5, 0xbc68f04d, 0xbe0bf09b, 0xbedaa462, 0xbf21e8ea, 0xbfb12b5e, 0xbfcb3846, 0xc18efd46,
           0x3eec42f2, 0x3f88d884, 0xc12fc40a, 0x3ed125d4, 0x432a78dd, 0x3f28a5cd, 0x3f3f8e4c, 0x400735c0);
};

// Simple random test with similar values + 1 subnormal (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //              -0.8057, -0.8564,  0.3425, -0.3066, -0.7314, -0.6396,  0.7588,
  //              -0.3743,  0.8706, -0.3064,  0.0390,  0.6123,  0.0237, -0.6201,
  //              -0.4524,  0.3337
  VLOAD_16(v2, 0xba72, 0xbada, 0x357b, 0xb4e8, 0xb9da, 0xb91e, 0x3a12, 0xb5fd, 0x3af7, 0xb4e7, 0x28fe, 0x38e6, 0x2612,
           0xb8f6, 0xb73d, 0x3557);
  //              -0.4094,  0.0410, -0.7305,  0.9038, -0.3545,  0.2830, -0.7051,
  //              -0.7124, -0.6348,  0.1256,  0.5576,  0.1334,  0.8779, -0.4836,
  //              0.3215,  0.4167
  VLOAD_16(v3, 0xb68d, 0x293e, 0xb9d8, 0x3b3b, 0xb5ac, 0x3487, 0xb9a4, 0xb9b3, 0xb914, 0x3005, 0x3876, 0x3045, 0x3b06,
           0xb7bd, 0x3525, 0x36ab);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vfdiv.vv v1, v2, v3, v0.t");
  //               0.0000, -20.9062,  0.0000, -0.3394,  0.0000, -2.2598, 0.0000,
  //               0.5254,  0.0000, -2.4395,  0.0000,  4.5898,  0.0000,  1.2822,
  //               0.0000,  0.8008
  VCMP_U16(4, v1, 0x0, 0xcd3a, 0x0, 0xb56d, 0x0, 0xc085, 0x0, 0x3833, 0x0, 0xc0e0, 0x0, 0x4496, 0x0, 0x3d20, 0x0,
           0x3a68);

  VSET(16, e32, m2);
  //               0.64838839,  0.00666664, -0.13619921,  0.21094505,
  //               -0.51040554, -0.77216595,  0.42111391,  0.82974166,
  //               -0.31227046,  0.68854737, -0.72970057,  0.10843290,
  //               -0.38442346,  0.18102080,  0.57249051,  0.76465768
  VLOAD_32(v4, 0x3f25fcc8, 0x3bda73da, 0xbe0b77ce, 0x3e5801fb, 0xbf02a9f0, 0xbf45acab, 0x3ed79c3e, 0x3f5469f3,
           0xbe9fe1ea, 0x3f3044a4, 0xbf3acda8, 0x3dde1212, 0xbec4d327, 0x3e395d84, 0x3f128ebd, 0x3f43c09b);
  //              -0.59629226, -0.46890569,  0.99662799, -0.49397555,
  //              0.80701596,  0.55786854, -0.26524273, -0.04642257,
  //              -0.67671824,  0.64403933,  0.06642481,  0.26544699,
  //              -0.00225505,  0.27478188,  0.76509053,  0.36194146
  VLOAD_32(v6, 0xbf18a69c, 0xbef01468, 0x3f7f2303, 0xbefcea5d, 0x3f4e9899, 0x3f0ed079, 0xbe87cde5, 0xbd3e2597,
           0xbf2d3d68, 0x3f24dfc3, 0x3d8809bb, 0x3e87e8ab, 0xbb13c97d, 0x3e8cb036, 0x3f43dcf9, 0x3eb95064);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v2);
  asm volatile("vfdiv.vv v2, v4, v6, v0.t");
  //               0.00000000, -0.01421745,  0.00000000, -0.42703542,
  //               0.00000000, -1.38413608,  0.00000000, -17.87367058,
  //               0.00000000,  1.06910765,  0.00000000,  0.40849173,
  //               0.00000000,  0.65877998,  0.00000000,  2.11265564
  VCMP_U32(5, v2, 0x0, 0xbc68f04d, 0x0, 0xbedaa462, 0x0, 0xbfb12b5e, 0x0, 0xc18efd46, 0x0, 0x3f88d884, 0x0, 0x3ed125d4,
           0x0, 0x3f28a5cd, 0x0, 0x400735c0);
};

// Simple random test with similar values (vector-scalar)
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  //              -0.0933,  0.4983,  0.5918, -0.0608,  0.0790, -0.2864, -0.7656,
  //              0.4878,  0.8862,  0.4255,  0.9561, -0.7158, -0.3247,  0.9961,
  //              -0.4963, -0.4114
  VLOAD_16(v2, 0xadf9, 0x37f9, 0x38bc, 0xabc7, 0x2d0f, 0xb495, 0xba20, 0x37ce, 0x3b17, 0x36cf, 0x3ba6, 0xb9ba, 0xb532,
           0x3bf8, 0xb7f1, 0xb695);
  float fscalar_16;
  //                             -0.3206
  BOX_HALF_IN_FLOAT(fscalar_16, 0xb521);
  asm volatile("vfdiv.vf v1, v2, %[A]" ::[A] "f"(fscalar_16));
  //               0.2910, -1.5547, -1.8457,  0.1896, -0.2466,  0.8936,  2.3887,
  //               -1.5215, -2.7656, -1.3271, -2.9824,  2.2324,  1.0127,
  //               -3.1074,  1.5488,  1.2832
  VCMP_U16(7, v1, 0x34a8, 0xbe37, 0xbf62, 0x3210, 0xb3e3, 0x3b25, 0x40c6, 0xbe16, 0xc187, 0xbd4f, 0xc1f7, 0x4077,
           0x3c0d, 0xc236, 0x3e31, 0x3d22);

  VSET(16, e32, m2);
  //               0.74354362,  0.49774653,  0.25714639,  0.51635689,
  //               0.74569613,  0.41876560,  0.21346331,  0.08743033,
  //               -0.15111920, -0.93289024,  0.08753468, -0.33427054,
  //               0.06167563, -0.54564798,  0.78990245, -0.77273035
  VLOAD_32(v4, 0x3f3e58e0, 0x3efed8a2, 0x3e83a8b1, 0x3f042ff7, 0x3f3ee5f1, 0x3ed66872, 0x3e5a9620, 0x3db30eac,
           0xbe1abefe, 0xbf6ed1e5, 0x3db34562, 0xbeab2582, 0x3d7c9f95, 0xbf0baf96, 0x3f4a370c, 0xbf45d1a8);
  float fscalar_32;
  //                              -0.45971388
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0xbeeb5f9e);
  asm volatile("vfdiv.vf v2, v4, %[A]" ::[A] "f"(fscalar_32));
  //              -1.61740518, -1.08273113, -0.55936182, -1.12321365,
  //              -1.62208748, -0.91092664, -0.46433949, -0.19018422,
  //              0.32872447,  2.02928448, -0.19041122,  0.72712737,
  //              -0.13416091,  1.18692958, -1.71824801,  1.68089414
  VCMP_U32(8, v2, 0xbfcf0722, 0xbf8a96ef, 0xbf0f3255, 0xbf8fc576, 0xbfcfa090, 0xbf69327c, 0xbeedbde7, 0xbe42bfa7,
           0x3ea84e93, 0x4001dfcc, 0xbe42fb28, 0x3f3a2504, 0xbe096179, 0x3f97ed4e, 0xbfdbef8c, 0x3fd72789);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  //               -0.0933,  0.4983,  0.5918, -0.0608,  0.0790, -0.2864,
  //               -0.7656,  0.4878,  0.8862,  0.4255,  0.9561, -0.7158,
  //               -0.3247,  0.9961, -0.4963, -0.4114
  VLOAD_16(v2, 0xadf9, 0x37f9, 0x38bc, 0xabc7, 0x2d0f, 0xb495, 0xba20, 0x37ce, 0x3b17, 0x36cf, 0x3ba6, 0xb9ba, 0xb532,
           0x3bf8, 0xb7f1, 0xb695);
  float fscalar_16;
  //                             -0.3206
  BOX_HALF_IN_FLOAT(fscalar_16, 0xb521);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v1);
  asm volatile("vfdiv.vf v1, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  //                0.0000, -1.5547,  0.0000,  0.1896,  0.0000,  0.8936, 0.0000,
  //                -1.5215,  0.0000, -1.3271,  0.0000,  2.2324,  0.0000,
  //                -3.1074,  0.0000,  1.2832
  VCMP_U16(10, v1, 0x0, 0xbe37, 0x0, 0x3210, 0x0, 0x3b25, 0x0, 0xbe16, 0x0, 0xbd4f, 0x0, 0x4077, 0x0, 0xc236, 0x0,
           0x3d22);

  VSET(16, e32, m2);
  //                0.74354362,  0.49774653,  0.25714639,  0.51635689,
  //                0.74569613,  0.41876560,  0.21346331,  0.08743033,
  //                -0.15111920, -0.93289024,  0.08753468, -0.33427054,
  //                0.06167563, -0.54564798,  0.78990245, -0.77273035
  VLOAD_32(v4, 0x3f3e58e0, 0x3efed8a2, 0x3e83a8b1, 0x3f042ff7, 0x3f3ee5f1, 0x3ed66872, 0x3e5a9620, 0x3db30eac,
           0xbe1abefe, 0xbf6ed1e5, 0x3db34562, 0xbeab2582, 0x3d7c9f95, 0xbf0baf96, 0x3f4a370c, 0xbf45d1a8);
  float fscalar_32;
  //                              -0.45971388
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0xbeeb5f9e);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v2);
  asm volatile("vfdiv.vf v2, v4, %[A], v0.t" ::[A] "f"(fscalar_32));
  //                0.00000000, -1.08273113,  0.00000000, -1.12321365,
  //                0.00000000, -0.91092664,  0.00000000, -0.19018422,
  //                0.00000000,  2.02928448,  0.00000000,  0.72712737,
  //                0.00000000,  1.18692958,  0.00000000,  1.68089414
  VCMP_U32(11, v2, 0x0, 0xbf8a96ef, 0x0, 0xbf8fc576, 0x0, 0xbf69327c, 0x0, 0xbe42bfa7, 0x0, 0x4001dfcc, 0x0, 0x3f3a2504,
           0x0, 0x3f97ed4e, 0x0, 0x3fd72789);
};

int main(void) {
  enable_vec();
  enable_fp();
  // Change RM to RTZ since there are issues with FDIV + RNE in fpnew
  // Update: there are issues also with RTZ...
  CHANGE_RM(RM_RTZ);

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  EXIT_CHECK();
}
