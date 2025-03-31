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
  //              -4628.000,   5116.000, -9928.000,   9392.000, -140.875,
  //              6112.000,   2598.000,   3210.000,   528.000, -3298.000,
  //              -3674.000,   368.250,   1712.000, -8584.000, -2080.000,
  //              4336.000
  VLOAD_16(v2, 0xec85, 0x6cff, 0xf0d9, 0x7096, 0xd867, 0x6df8, 0x6913, 0x6a45, 0x6020, 0xea71, 0xeb2d, 0x5dc1, 0x66b0,
           0xf031, 0xe810, 0x6c3c);
  asm volatile("vfsqrt.v v3, v2");
  //                nan,   71.500,   nan,   96.938,
  //                nan,   78.188,   50.969,   56.656,   22.984,   nan,
  //                nan,   19.188,   41.375,   nan,   nan,   65.875
  VCMP_U16(1, v3, 0x7e00, 0x5478, 0x7e00, 0x560e, 0x7e00, 0x54e2, 0x525f, 0x5315, 0x4dbe, 0x7e00, 0x7e00, 0x4ccc,
           0x512c, 0x7e00, 0x7e00, 0x541d);

  VSET(16, e32, m2);
  //                53688.590, -5719.180, -59560.355, -34640.023, -22323.398,
  //                -52381.586,   19136.160,   13055.238, -68576.781,
  //                -35066.488,   62475.219, -25604.578,   54705.039,
  //                -19827.459,   17792.961, -28415.572
  VLOAD_32(v4, 0x4751b897, 0xc5b2b971, 0xc768a85b, 0xc7075006, 0xc6ae66cc, 0xc74c9d96, 0x46958052, 0x464bfcf4,
           0xc785f064, 0xc708fa7d, 0x47740b38, 0xc6c80928, 0x4755b10a, 0xc69ae6eb, 0x468b01ec, 0xc6ddff25);
  asm volatile("vfsqrt.v v6, v4");
  //                231.708,   nan,   nan,   nan,   nan,   nan,   138.334,
  //                114.260,   nan,   nan,   249.950,   nan,   233.891,   nan,
  //                133.390,   nan
  VCMP_U32(2, v6, 0x4367b53e, 0x7fc00000, 0x7fc00000, 0x7fc00000, 0x7fc00000, 0x7fc00000, 0x430a5560, 0x42e484e0,
           0x7fc00000, 0x7fc00000, 0x4379f34f, 0x7fc00000, 0x4369e41e, 0x7fc00000, 0x430563e7, 0x7fc00000);
};

// Simple random test with similar values (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //              -4628.000,   5116.000, -9928.000,   9392.000, -140.875,
  //              6112.000,   2598.000,   3210.000,   528.000, -3298.000,
  //              -3674.000,   368.250,   1712.000, -8584.000, -2080.000,
  //              4336.000
  VLOAD_16(v2, 0xec85, 0x6cff, 0xf0d9, 0x7096, 0xd867, 0x6df8, 0x6913, 0x6a45, 0x6020, 0xea71, 0xeb2d, 0x5dc1, 0x66b0,
           0xf031, 0xe810, 0x6c3c);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v3);
  asm volatile("vfsqrt.v v3, v2, v0.t");
  //                0.000,   71.500,   0.000,   96.938,   0.000,   78.188,
  //                0.000,   56.656,   0.000,   nan,   0.000,   19.188,   0.000,
  //                nan,   0.000,   65.875
  VCMP_U16(4, v3, 0x0, 0x5478, 0x0, 0x560e, 0x0, 0x54e2, 0x0, 0x5315, 0x0, 0x7e00, 0x0, 0x4ccc, 0x0, 0x7e00, 0x0,
           0x541d);

  VSET(16, e32, m2);
  //                53688.590, -5719.180, -59560.355, -34640.023, -22323.398,
  //                -52381.586,   19136.160,   13055.238, -68576.781,
  //                -35066.488,   62475.219, -25604.578,   54705.039,
  //                -19827.459,   17792.961, -28415.572
  VLOAD_32(v4, 0x4751b897, 0xc5b2b971, 0xc768a85b, 0xc7075006, 0xc6ae66cc, 0xc74c9d96, 0x46958052, 0x464bfcf4,
           0xc785f064, 0xc708fa7d, 0x47740b38, 0xc6c80928, 0x4755b10a, 0xc69ae6eb, 0x468b01ec, 0xc6ddff25);
  VLOAD_8(v0, 0xAA, 0xAA);
  VCLEAR(v6);
  asm volatile("vfsqrt.v v6, v4, v0.t");
  //                0.000,   nan,   0.000,   nan,   0.000,   nan,   0.000,
  //                114.260,   0.000,   nan,   0.000,   nan,   0.000,   nan,
  //                0.000,   nan
  VCMP_U32(5, v6, 0x0, 0x7fc00000, 0x0, 0x7fc00000, 0x0, 0x7fc00000, 0x0, 0x42e484e0, 0x0, 0x7fc00000, 0x0, 0x7fc00000,
           0x0, 0x7fc00000, 0x0, 0x7fc00000);
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
