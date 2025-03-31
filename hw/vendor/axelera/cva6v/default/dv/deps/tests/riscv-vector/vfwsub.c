// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>
//         Matteo Perotti <mperotti@iis.ee.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

// Simple random test with similar values
void TEST_CASE1(void) {
  VSET(16, e16, m1);
  //              -15.5625,  95.7500, -42.4375,  30.7188, -50.7500, -90.2500,
  //              -95.5000,  29.5938, -41.4062, -94.0000,  34.3438,
  //              -69.5625,  31.5625, -75.0625,  46.2500, -63.6875
  VLOAD_16(v2, 0xcbc8, 0x55fc, 0xd14e, 0x4fae, 0xd258, 0xd5a4, 0xd5f8, 0x4f66, 0xd12d, 0xd5e0, 0x504b, 0xd459, 0x4fe4,
           0xd4b1, 0x51c8, 0xd3f6);
  //               57.2500,  43.2812, -49.4062, -53.5625, -54.7812,
  //               -12.1406,  92.1875,  67.1875, -19.7656, -41.2812,  98.0625,
  //               -41.9062,  10.1719, -84.6250, -7.1016,  62.8750
  VLOAD_16(v6, 0x5328, 0x5169, 0xd22d, 0xd2b2, 0xd2d9, 0xca12, 0x55c3, 0x5433, 0xccf1, 0xd129, 0x5621, 0xd13d, 0x4916,
           0xd54a, 0xc71a, 0x53dc);
  asm volatile("vfwsub.vv v4, v2, v6");
  //              -72.81250000,  52.46875000,  6.96875000,  84.28125000,  4.03125000,
  //              -78.10937500, -187.68750000, -37.59375000, -21.64062500,
  //              -52.71875000, -63.71875000,
  //              -27.65625000,  21.39062500,  9.56250000,  53.35156250,
  //              -126.56250000
  VCMP_U32(1, v4, 0xc291a000, 0x4251e000, 0x40df0000, 0x42a89000, 0x40810000, 0xc29c3800, 0xc33bb000, 0xc2166000,
           0xc1ad2000, 0xc252e000, 0xc27ee000, 0xc1dd4000, 0x41ab2000, 0x41190000, 0x42556800, 0xc2fd2000);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //              -15.5625,  95.7500, -42.4375,  30.7188, -50.7500, -90.2500,
  //              -95.5000,  29.5938, -41.4062, -94.0000,  34.3438,
  //              -69.5625,  31.5625, -75.0625,  46.2500, -63.6875
  VLOAD_16(v2, 0xcbc8, 0x55fc, 0xd14e, 0x4fae, 0xd258, 0xd5a4, 0xd5f8, 0x4f66, 0xd12d, 0xd5e0, 0x504b, 0xd459, 0x4fe4,
           0xd4b1, 0x51c8, 0xd3f6);
  //               57.2500,  43.2812, -49.4062, -53.5625, -54.7812,
  //               -12.1406,  92.1875,  67.1875, -19.7656, -41.2812,  98.0625,
  //               -41.9062,  10.1719, -84.6250, -7.1016,  62.8750
  VLOAD_16(v6, 0x5328, 0x5169, 0xd22d, 0xd2b2, 0xd2d9, 0xca12, 0x55c3, 0x5433, 0xccf1, 0xd129, 0x5621, 0xd13d, 0x4916,
           0xd54a, 0xc71a, 0x53dc);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwsub.vv v4, v2, v6, v0.t");
  //               0.00000000,  52.46875000,  0.00000000,  84.28125000,
  //               0.00000000, -78.10937500,  0.00000000, -37.59375000,
  //               0.00000000, -52.71875000,  0.00000000, -27.65625000,
  //               0.00000000,  9.56250000,  0.00000000, -126.56250000
  VCMP_U32(2, v4, 0x0, 0x4251e000, 0x0, 0x42a89000, 0x0, 0xc29c3800, 0x0, 0xc2166000, 0x0, 0xc252e000, 0x0, 0xc1dd4000,
           0x0, 0x41190000, 0x0, 0xc2fd2000);
};

// Simple random test with similar values (vector-scalar)
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                              36.4375
  BOX_HALF_IN_FLOAT(fscalar_16, 0x508e);
  //               69.8125, -37.3125, -77.2500,  32.7188,
  //               -83.0000,  76.3125,  14.9375,  72.5000,  39.6250,
  //               -61.2188,  36.3438,  93.5000, -87.1875, -6.9258,  25.1094,
  //               -96.8750
  VLOAD_16(v2, 0x545d, 0xd0aa, 0xd4d4, 0x5017, 0xd530, 0x54c5, 0x4b78, 0x5488, 0x50f4, 0xd3a7, 0x508b, 0x55d8, 0xd573,
           0xc6ed, 0x4e47, 0xd60e);
  asm volatile("vfwsub.vf v4, v2, %[A]" ::[A] "f"(fscalar_16));
  //               33.37500000, -73.75000000, -113.68750000, -3.71875000,
  //               -119.43750000,  39.87500000,
  //               -21.50000000,  36.06250000,  3.18750000, -97.65625000,
  //               -0.09375000,  57.06250000, -123.62500000, -43.36328125,
  //               -11.32812500, -133.31250000
  VCMP_U32(3, v4, 0x42058000, 0xc2938000, 0xc2e36000, 0xc06e0000, 0xc2eee000, 0x421f8000, 0xc1ac0000, 0x42104000,
           0x404c0000, 0xc2c35000, 0xbdc00000, 0x42644000, 0xc2f74000, 0xc22d7400, 0xc1354000, 0xc3055000);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                              36.4375
  BOX_HALF_IN_FLOAT(fscalar_16, 0x508e);
  //                69.8125, -37.3125, -77.2500,  32.7188,
  //                -83.0000,  76.3125,  14.9375,  72.5000,  39.6250,
  //                -61.2188,  36.3438,  93.5000, -87.1875, -6.9258,  25.1094,
  //                -96.8750
  VLOAD_16(v2, 0x545d, 0xd0aa, 0xd4d4, 0x5017, 0xd530, 0x54c5, 0x4b78, 0x5488, 0x50f4, 0xd3a7, 0x508b, 0x55d8, 0xd573,
           0xc6ed, 0x4e47, 0xd60e);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwsub.vf v4, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  //                0.00000000, -73.75000000,  0.00000000, -3.71875000,
  //                0.00000000,  39.87500000,  0.00000000,  36.06250000,
  //                0.00000000, -97.65625000,  0.00000000,  57.06250000,
  //                0.00000000, -43.36328125,  0.00000000, -133.31250000
  VCMP_U32(4, v4, 0x0, 0xc2938000, 0x0, 0xc06e0000, 0x0, 0x421f8000, 0x0, 0x42104000, 0x0, 0xc2c35000, 0x0, 0x42644000,
           0x0, 0xc22d7400, 0x0, 0xc3055000);
};
// Simple random test with similar values
void TEST_CASE5(void) {
  VSET(16, e16, m1);
  //              -92.15529633,  27.66998672,
  //              -5.68499708,  78.95133209,  57.52299500,  15.45270920,  50.26883316,
  //              46.63587189,  71.16806793, -80.68485260,
  //              -22.34193420,  40.17027283,  93.54611969,  25.86016083,  41.82838821,
  //              82.50254822
  VLOAD_32(v2, 0xc2b84f83, 0x41dd5c22, 0xc0b5eb7f, 0x429de715, 0x4266178c, 0x41773e4c, 0x42491349, 0x423a8b22,
           0x428e560d, 0xc2a15ea5, 0xc1b2bc48, 0x4220ae5c, 0x42bb179d, 0x41cee19c, 0x42275045, 0x42a5014e);
  //              -72.5625, -83.4375,  28.8281,  33.5938,
  //              -85.7500,  67.5000,  91.0625, -91.8750, -9.2578, -64.2500,
  //              -58.6250,  50.3438, -70.5000,  36.6250,  5.7930,  86.6875
  VLOAD_16(v6, 0xd489, 0xd537, 0x4f35, 0x5033, 0xd55c, 0x5438, 0x55b1, 0xd5be, 0xc8a1, 0xd404, 0xd354, 0x524b, 0xd468,
           0x5094, 0x45cb, 0x556b);
  asm volatile("vfwsub.wv v4, v2, v6");
  //              -19.59279633,  111.10748291, -34.51312256,  45.35758209,
  //              143.27299500, -52.04729080, -40.79366684,
  //              138.51086426,  80.42588043, -16.43485260,  36.28306580,
  //              -10.17347717,  164.04611206, -10.76483917,  36.03541946,
  //              -4.18495178
  VCMP_U32(5, v4, 0xc19cbe0c, 0x42de3708, 0xc20a0d70, 0x42356e2a, 0x430f45e3, 0xc250306d, 0xc2232cb7, 0x430a82c8,
           0x42a0da0d, 0xc1837a94, 0x421121dc, 0xc122c690, 0x43240bce, 0xc12c3cc8, 0x42102445, 0xc085eb20);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE6(void) {
  VSET(16, e16, m1);
  //              -92.15529633,  27.66998672,
  //              -5.68499708,  78.95133209,  57.52299500,  15.45270920,  50.26883316,
  //              46.63587189,  71.16806793, -80.68485260,
  //              -22.34193420,  40.17027283,  93.54611969,  25.86016083,  41.82838821,
  //              82.50254822
  VLOAD_32(v2, 0xc2b84f83, 0x41dd5c22, 0xc0b5eb7f, 0x429de715, 0x4266178c, 0x41773e4c, 0x42491349, 0x423a8b22,
           0x428e560d, 0xc2a15ea5, 0xc1b2bc48, 0x4220ae5c, 0x42bb179d, 0x41cee19c, 0x42275045, 0x42a5014e);
  //              -72.5625, -83.4375,  28.8281,  33.5938,
  //              -85.7500,  67.5000,  91.0625, -91.8750, -9.2578, -64.2500,
  //              -58.6250,  50.3438, -70.5000,  36.6250,  5.7930,  86.6875
  VLOAD_16(v6, 0xd489, 0xd537, 0x4f35, 0x5033, 0xd55c, 0x5438, 0x55b1, 0xd5be, 0xc8a1, 0xd404, 0xd354, 0x524b, 0xd468,
           0x5094, 0x45cb, 0x556b);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwsub.wv v4, v2, v6, v0.t");
  //               0.00000000,  111.10748291,  0.00000000,  45.35758209,
  //               0.00000000, -52.04729080,  0.00000000,  138.51086426,
  //               0.00000000, -16.43485260,  0.00000000, -10.17347717,
  //               0.00000000, -10.76483917,  0.00000000, -4.18495178
  VCMP_U32(6, v4, 0x0, 0x42de3708, 0x0, 0x42356e2a, 0x0, 0xc250306d, 0x0, 0x430a82c8, 0x0, 0xc1837a94, 0x0, 0xc122c690,
           0x0, 0xc12c3cc8, 0x0, 0xc085eb20);
};

// Simple random test with similar values (vector-scalar)
void TEST_CASE7(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //              -8.76965809,  55.45920181,  71.29286957, -84.65414429,
  //              -81.93881226,  75.13192749, -75.44019318, -48.81898499,
  //              0.10306206, -25.18898392,  49.68006516,  72.66278076,
  //              -24.90880966, -32.59431458,  14.58876038, -55.07221603
  VLOAD_32(v2, 0xc10c5085, 0x425dd639, 0x428e95f3, 0xc2a94eec, 0xc2a3e0ac, 0x4296438c, 0xc296e161, 0xc24346a4,
           0x3dd31233, 0xc1c9830a, 0x4246b863, 0x42915358, 0xc1c7453e, 0xc2026094, 0x41696b90, 0xc25c49f3);
  //                              34.7812
  BOX_HALF_IN_FLOAT(fscalar_16, 0x5059);
  asm volatile("vfwsub.wf v4, v2, %[A]" ::[A] "f"(fscalar_16));
  //              -43.55090714,  20.67795181,  36.51161957, -119.43539429,
  //              -116.72006226,  40.35067749, -110.22144318, -83.60023499,
  //              -34.67818832, -59.97023392,  14.89881516,  37.88153076,
  //              -59.69005966, -67.37556458, -20.19248962, -89.85346985
  VCMP_U32(7, v4, 0xc22e3421, 0x41a56c72, 0x42120be6, 0xc2eedeec, 0xc2e970ac, 0x42216718, 0xc2dc7161, 0xc2a73352,
           0xc20ab677, 0xc26fe185, 0x416e618c, 0x421786b0, 0xc26ec29f, 0xc286c04a, 0xc1a18a38, 0xc2b3b4fa);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE8(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //               -8.76965809,  55.45920181,  71.29286957, -84.65414429,
  //               -81.93881226,  75.13192749, -75.44019318, -48.81898499,
  //               0.10306206, -25.18898392,  49.68006516,  72.66278076,
  //               -24.90880966, -32.59431458,  14.58876038, -55.07221603
  VLOAD_32(v2, 0xc10c5085, 0x425dd639, 0x428e95f3, 0xc2a94eec, 0xc2a3e0ac, 0x4296438c, 0xc296e161, 0xc24346a4,
           0x3dd31233, 0xc1c9830a, 0x4246b863, 0x42915358, 0xc1c7453e, 0xc2026094, 0x41696b90, 0xc25c49f3);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  //                              34.7812
  BOX_HALF_IN_FLOAT(fscalar_16, 0x5059);
  asm volatile("vfwsub.wf v4, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  //                0.00000000,  20.67795181,  0.00000000, -119.43539429,
  //                0.00000000,  40.35067749,  0.00000000, -83.60023499,
  //                0.00000000, -59.97023392,  0.00000000,  37.88153076,
  //                0.00000000, -67.37556458,  0.00000000, -89.85346985
  VCMP_U32(8, v4, 0x0, 0x41a56c72, 0x0, 0xc2eedeec, 0x0, 0x42216718, 0x0, 0xc2a73352, 0x0, 0xc26fe185, 0x0, 0x421786b0,
           0x0, 0xc286c04a, 0x0, 0xc2b3b4fa);
};

int main(void) {
  enable_vec();
  enable_fp();

  // TEST_CASE1();
  // MASKED_TEST(TEST_CASE2());
  // TEST_CASE3();
  // MASKED_TEST(TEST_CASE4());

  TEST_CASE5();
  MASKED_TEST(TEST_CASE6());
  TEST_CASE7();
  MASKED_TEST(TEST_CASE8());

  EXIT_CHECK();
}
