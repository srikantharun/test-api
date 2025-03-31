// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>
//         Matteo Perotti <mperotti@iis.ee.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

// Simple random test with similar values (vector-scalar)
void TEST_CASE1(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //              -35.5312, -61.8125, -37.3125,  23.5938,  44.4688,  38.1250,
  //              -93.5000, -23.2031, -62.8125,  27.9844, -26.2344, -10.3594,
  //              -10.7109, -42.0938,  11.0625,  17.8281
  VLOAD_16(v2, 0xd071, 0xd3ba, 0xd0aa, 0x4de6, 0x518f, 0x50c4, 0xd5d8, 0xcdcd, 0xd3da, 0x4eff, 0xce8f, 0xc92e, 0xc95b,
           0xd143, 0x4988, 0x4c75);
  //                             -17.4844
  BOX_HALF_IN_FLOAT(fscalar_16, 0xcc5f);
  asm volatile("vfrdiv.vf v4, v2, %[A]" ::[A] "f"(fscalar_16));
  //               0.4922,  0.2830,  0.4685, -0.7412, -0.3931, -0.4585,  0.1870,
  //               0.7534,  0.2783, -0.6250,  0.6665,  1.6875,  1.6328,  0.4153,
  //               -1.5801, -0.9810
  VCMP_U16(1, v4, 0x37df, 0x3486, 0x377f, 0xb9ed, 0xb64a, 0xb756, 0x31fb, 0x3a07, 0x3474, 0xb8ff, 0x3954, 0x3ec0,
           0x3e87, 0x36a5, 0xbe52, 0xbbd8);

  VSET(16, e32, m2);
  float fscalar_32;
  //               981163.06250000, -831670.37500000, -85439.06250000,
  //               64225.75781250, -215361.43750000, -292944.75000000,
  //               396490.21875000,  954345.93750000,  241910.40625000,
  //               -62372.83593750,  391838.50000000,  263890.03125000,
  //               755217.06250000, -6653.31689453,  526939.25000000,
  //               -759232.75000000
  VLOAD_32(v4, 0x496f8ab1, 0xc94b0b66, 0xc7a6df88, 0x477ae1c2, 0xc852505c, 0xc88f0a18, 0x48c19947, 0x4968fe9f,
           0x486c3d9a, 0xc773a4d6, 0x48bf53d0, 0x4880da41, 0x49386111, 0xc5cfea89, 0x4900a5b4, 0xc9395c0c);
  //                              -816463.43750000
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0xc94754f7);
  asm volatile("vfrdiv.vf v8, v4, %[A]" ::[A] "f"(fscalar_32));
  //              -0.83213836,  0.98171520,  9.55609035,
  //              -12.71239853,  3.79113102,  2.78709030, -2.05922723,
  //              -0.85552144, -3.37506533,  13.09004879, -2.08367324,
  //              -3.09395337, -1.08109772,  122.71524811,
  //              -1.54944515,  1.07537961
  VCMP_U32(2, v8, 0xbf550705, 0x3f7b51af, 0x4118e5bf, 0xc14b65fc, 0x4072a1e4, 0x40325faf, 0xc003ca60, 0xbf5b0374,
           0xc0580112, 0x415170d6, 0xc0055ae7, 0xc0460354, 0xbf8a6168, 0x42f56e35, 0xbfc65437, 0x3f89a60a);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //               -35.5312, -61.8125, -37.3125,  23.5938,  44.4688,  38.1250,
  //               -93.5000, -23.2031, -62.8125,  27.9844, -26.2344, -10.3594,
  //               -10.7109, -42.0938,  11.0625,  17.8281
  VLOAD_16(v2, 0xd071, 0xd3ba, 0xd0aa, 0x4de6, 0x518f, 0x50c4, 0xd5d8, 0xcdcd, 0xd3da, 0x4eff, 0xce8f, 0xc92e, 0xc95b,
           0xd143, 0x4988, 0x4c75);
  //                             -17.4844
  BOX_HALF_IN_FLOAT(fscalar_16, 0xcc5f);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v4);
  asm volatile("vfrdiv.vf v4, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  //                0.0000,  0.2830,  0.0000, -0.7412,  0.0000, -0.4585, 0.0000,
  //                0.7534,  0.0000, -0.6250,  0.0000,  1.6875,  0.0000, 0.4153,
  //                0.0000, -0.9810
  VCMP_U16(4, v4, 0x0, 0x3486, 0x0, 0xb9ed, 0x0, 0xb756, 0x0, 0x3a07, 0x0, 0xb8ff, 0x0, 0x3ec0, 0x0, 0x36a5, 0x0,
           0xbbd8);

  VSET(16, e32, m2);
  float fscalar_32;
  //                981163.06250000, -831670.37500000, -85439.06250000,
  //                64225.75781250, -215361.43750000, -292944.75000000,
  //                396490.21875000,  954345.93750000,  241910.40625000,
  //                -62372.83593750,  391838.50000000,  263890.03125000,
  //                755217.06250000, -6653.31689453,  526939.25000000,
  //                -759232.75000000
  VLOAD_32(v4, 0x496f8ab1, 0xc94b0b66, 0xc7a6df88, 0x477ae1c2, 0xc852505c, 0xc88f0a18, 0x48c19947, 0x4968fe9f,
           0x486c3d9a, 0xc773a4d6, 0x48bf53d0, 0x4880da41, 0x49386111, 0xc5cfea89, 0x4900a5b4, 0xc9395c0c);
  //                              -816463.43750000
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0xc94754f7);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v8);
  asm volatile("vfrdiv.vf v8, v4, %[A], v0.t" ::[A] "f"(fscalar_32));
  //                0.00000000,  0.98171520,  0.00000000, -12.71239853,
  //                0.00000000,  2.78709030,  0.00000000, -0.85552144,
  //                0.00000000,  13.09004879,  0.00000000, -3.09395337,
  //                0.00000000,  122.71524811,  0.00000000,  1.07537961
  VCMP_U32(5, v8, 0x0, 0x3f7b51af, 0x0, 0xc14b65fc, 0x0, 0x40325faf, 0x0, 0xbf5b0374, 0x0, 0x415170d6, 0x0, 0xc0460354,
           0x0, 0x42f56e35, 0x0, 0x3f89a60a);
};

int main(void) {
  enable_vec();
  enable_fp();
  // Change RM to RTZ since there are issues with FDIV + RNE in fpnew
  // Update: there are issues also with RTZ...
  CHANGE_RM(RM_RTZ);

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());

  EXIT_CHECK();
}
