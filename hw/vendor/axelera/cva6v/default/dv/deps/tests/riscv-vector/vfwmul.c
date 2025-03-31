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
  //              -56.5312,  95.3750,  86.3750, -33.4375,  4.7656,  58.8438,
  //              -80.4375, -96.4375,  74.3750, -92.7500, -57.2812, -90.0625,
  //              -93.2500,  40.6875, -32.2812, -36.8125
  VLOAD_16(v2, 0xd311, 0x55f6, 0x5566, 0xd02e, 0x44c4, 0x535b, 0xd507, 0xd607, 0x54a6, 0xd5cc, 0xd329, 0xd5a1, 0xd5d4,
           0x5116, 0xd009, 0xd09a);
  //               96.4375, -98.8125, -49.1250, -78.8750,
  //               -5.9180,  32.8750,  32.8750, -74.8125,
  //               -10.3750,  39.5938,  43.2812,  15.0547, -31.9062,
  //               -11.2500,  16.3594,  28.6094
  VLOAD_16(v6, 0x5607, 0xd62d, 0xd224, 0xd4ee, 0xc5eb, 0x501c, 0x501c, 0xd4ad, 0xc930, 0x50f3, 0x5169, 0x4b87, 0xcffa,
           0xc9a0, 0x4c17, 0x4f27);
  asm volatile("vfwmul.vv v4, v2, v6");
  //              -5451.73242188, -9424.24218750, -4243.17187500, 2637.38281250,
  //              -28.20281982,  1934.48828125, -2644.38281250,  7214.73046875,
  //              -771.64062500, -3672.32031250, -2479.20410156, -1355.86279297,
  //              2975.25781250, -457.73437500, -528.10107422, -1053.18261719
  VCMP_U32(1, v4, 0xc5aa5ddc, 0xc61340f8, 0xc5849960, 0x4524d620, 0xc1e19f60, 0x44f1cfa0, 0xc5254620, 0x45e175d8,
           0xc440e900, 0xc5658520, 0xc51af344, 0xc4a97b9c, 0x4539f420, 0xc3e4de00, 0xc4040678, 0xc483a5d8);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //              -56.5312,  95.3750,  86.3750, -33.4375,  4.7656,  58.8438,
  //              -80.4375, -96.4375,  74.3750, -92.7500, -57.2812, -90.0625,
  //              -93.2500,  40.6875, -32.2812, -36.8125
  VLOAD_16(v2, 0xd311, 0x55f6, 0x5566, 0xd02e, 0x44c4, 0x535b, 0xd507, 0xd607, 0x54a6, 0xd5cc, 0xd329, 0xd5a1, 0xd5d4,
           0x5116, 0xd009, 0xd09a);
  //               96.4375, -98.8125, -49.1250, -78.8750,
  //               -5.9180,  32.8750,  32.8750, -74.8125,
  //               -10.3750,  39.5938,  43.2812,  15.0547, -31.9062,
  //               -11.2500,  16.3594,  28.6094
  VLOAD_16(v6, 0x5607, 0xd62d, 0xd224, 0xd4ee, 0xc5eb, 0x501c, 0x501c, 0xd4ad, 0xc930, 0x50f3, 0x5169, 0x4b87, 0xcffa,
           0xc9a0, 0x4c17, 0x4f27);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  asm volatile("vfwmul.vv v4, v2, v6, v0.t");
  //               0.00000000, -9424.24218750,  0.00000000,  2637.38281250,
  //               0.00000000,  1934.48828125,  0.00000000,  7214.73046875,
  //               0.00000000, -3672.32031250,  0.00000000, -1355.86279297,
  //               0.00000000, -457.73437500,  0.00000000, -1053.18261719
  VCMP_U32(2, v4, 0x0, 0xc61340f8, 0x0, 0x4524d620, 0x0, 0x44f1cfa0, 0x0, 0x45e175d8, 0x0, 0xc5658520, 0x0, 0xc4a97b9c,
           0x0, 0xc3e4de00, 0x0, 0xc483a5d8);
};

// Simple random test with similar values (vector-scalar)
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //              -44.4062, -27.0781, -21.6562,  75.5625, -84.5000,
  //              -1.0713,  72.5625, -84.6250,  83.9375, -52.3438,
  //              -40.5625,  1.6523,  79.6875, -36.2812,  33.5938, -72.4375
  VLOAD_16(v2, 0xd18d, 0xcec5, 0xcd6a, 0x54b9, 0xd548, 0xbc49, 0x5489, 0xd54a, 0x553f, 0xd28b, 0xd112, 0x3e9c, 0x54fb,
           0xd089, 0x5033, 0xd487);
  //                             -58.9688
  BOX_HALF_IN_FLOAT(fscalar_16, 0xd35f);
  asm volatile("vfwmul.vf v4, v2, %[A]" ::[A] "f"(fscalar_16));
  //               2618.58105469,  1596.76318359,  1277.04199219,
  //               -4455.82617188,  4982.85937500,  63.17257690, -4278.91992188,
  //               4990.23046875, -4949.68945312,  3086.64550781, 2391.91992188,
  //               -97.43664551, -4699.07226562,  2139.45996094, -1980.98144531,
  //               4271.54882812
  VCMP_U32(3, v4, 0x4523a94c, 0x44c7986c, 0x449fa158, 0xc58b3e9c, 0x459bb6e0, 0x427cb0b8, 0xc585b75c, 0x459bf1d8,
           0xc59aad84, 0x4540ea54, 0x45157eb8, 0xc2c2df90, 0xc592d894, 0x4505b75c, 0xc4f79f68, 0x45857c64);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //               -44.4062, -27.0781, -21.6562,  75.5625, -84.5000,
  //               -1.0713,  72.5625, -84.6250,  83.9375, -52.3438,
  //               -40.5625,  1.6523,  79.6875, -36.2812,  33.5938, -72.4375
  VLOAD_16(v2, 0xd18d, 0xcec5, 0xcd6a, 0x54b9, 0xd548, 0xbc49, 0x5489, 0xd54a, 0x553f, 0xd28b, 0xd112, 0x3e9c, 0x54fb,
           0xd089, 0x5033, 0xd487);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  VCLEAR(v5);
  //                             -58.9688
  BOX_HALF_IN_FLOAT(fscalar_16, 0xd35f);
  asm volatile("vfwmul.vf v4, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  //                0.00000000,  1596.76318359,  0.00000000, -4455.82617188,
  //                0.00000000,  63.17257690,  0.00000000,  4990.23046875,
  //                0.00000000,  3086.64550781,  0.00000000, -97.43664551,
  //                0.00000000,  2139.45996094,  0.00000000,  4271.54882812
  VCMP_U32(4, v4, 0x0, 0x44c7986c, 0x0, 0xc58b3e9c, 0x0, 0x427cb0b8, 0x0, 0x459bf1d8, 0x0, 0x4540ea54, 0x0, 0xc2c2df90,
           0x0, 0x4505b75c, 0x0, 0x45857c64);
};

int main(void) {
  enable_vec();
  enable_fp();

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  EXIT_CHECK();
}
