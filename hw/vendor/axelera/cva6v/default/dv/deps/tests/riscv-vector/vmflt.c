// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Basile Bougenot <bbougenot@student.ethz.ch>
//         Matteo Perotti <mperotti@iis.ee.ethz.ch>

#include "float_macros.h"
#include "vector_macros.h"

// This instruction writes a mask to a register, with a layout of elements as
// described in section "Mask Register Layout"
void TEST_CASE1(void) {
  VSET(16, e16, m1);
  //               0.2434,  0.7285,  0.7241, -0.2678,  0.0027, -0.7114,  0.2622,
  //               0.8701, -0.5786, -0.4229,  0.5981,  0.6968,  0.7217, -0.2842,
  //               0.1328,  0.1659
  VLOAD_16(v2, 0x33ca, 0x39d4, 0x39cb, 0xb449, 0x1975, 0xb9b1, 0x3432, 0x3af6, 0xb8a1, 0xb6c4, 0x38c9, 0x3993, 0x39c6,
           0xb48c, 0x3040, 0x314f);
  //               0.7319,  0.0590,  0.7593, -0.6606, -0.4758,  0.8530,  0.0453,
  //               0.0987,  0.1777,  0.3047,  0.2330, -0.3467, -0.4153,  0.7080,
  //               0.3142, -0.9492
  VLOAD_16(v3, 0x39db, 0x2b8c, 0x3a13, 0xb949, 0xb79d, 0x3ad3, 0x29cc, 0x2e51, 0x31b0, 0x34e0, 0x3375, 0xb58c, 0xb6a5,
           0x39aa, 0x3041, 0xbb98);
  asm volatile("vmset.m v1");
  asm volatile("vmflt.vv v1, v2, v3");
  VSET(1, e16, m1);
  VCMP_U16(1, v1, 0x6325);

  VSET(16, e32, m2);
  //                       +0,        sNaN, -0.34645590, -0.06222415,
  //                       0.96037650, -0.81018746, -0.69337404,  0.70466602,
  //                       -0.30920035, -0.31596854, -0.92116749,  0.51336122,
  //                       0.22002794,  0.48599416,  0.69166088,  0.85755372
  VLOAD_32(v4, 0x00000000, 0xffffffff, 0xbeb162ab, 0xbd7edebf, 0x3f75db3c, 0xbf4f6872, 0xbf3180f6, 0x3f3464fe,
           0xbe9e4f82, 0xbea1c6a1, 0xbf6bd1a2, 0x3f036ba4, 0x3e614f01, 0x3ef8d43a, 0x3f3110b0, 0x3f5b88a4);
  //                       -0,        sNaN,  0.39402914, -0.81853813,
  //                       0.24656086, -0.71423489, -0.44735566, -0.25510681,
  //                       -0.94378990, -0.30138883,  0.19188073, -0.29310879,
  //                       -0.22981364, -0.58626360, -0.80913633, -0.00670803
  VLOAD_32(v6, 0x80000000, 0xffffffff, 0x3ec9be30, 0xbf518bb7, 0x3e7c7a73, 0xbf36d819, 0xbee50bcd, 0xbe829d5c,
           0xbf719c37, 0xbe9a4fa3, 0x3e447c62, 0xbe96125b, 0xbe6b5444, 0xbf16155f, 0xbf4f238f, 0xbbdbcefe);
  asm volatile("vmset.m v2");
  asm volatile("vmflt.vv v2, v4, v6");
  VSET(1, e16, m1);
  VCMP_U16(2, v2, 0x0664);
};

// Simple random test with similar values + 1 subnormal (masked)
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //               0.2434,  0.7285,  0.7241, -0.2678,  0.0027, -0.7114,  0.2622,
  //               0.8701, -0.5786, -0.4229,  0.5981,  0.6968,  0.7217, -0.2842,
  //               0.1328,  0.1659
  VLOAD_16(v2, 0x33ca, 0x39d4, 0x39cb, 0xb449, 0x1975, 0xb9b1, 0x3432, 0x3af6, 0xb8a1, 0xb6c4, 0x38c9, 0x3993, 0x39c6,
           0xb48c, 0x3040, 0x314f);
  //               0.7319,  0.7285,  0.7593, -0.6606, -0.4758,  0.8530,  0.0453,
  //               0.0987,  0.1777,  0.3047,  0.2330, -0.3467, -0.4153,  0.7080,
  //               0.3142, -0.9492
  VLOAD_16(v3, 0x39db, 0x39d4, 0x3a13, 0xb949, 0xb79d, 0x3ad3, 0x29cc, 0x2e51, 0x31b0, 0x34e0, 0x3375, 0xb58c, 0xb6a5,
           0x39aa, 0x3507, 0xbb98);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vmset.m v1");
  asm volatile("vmflt.vv v1, v2, v3, v0.t");
  VSET(1, e16, m1);
  VCMP_U16(4, v1, 0x7775);

  VSET(16, e32, m2);
  //               0x00000000,  0.09933749, -0.34645590, -0.06222415,
  //               0.96037650, -0.81018746, -0.69337404,  0.70466602,
  //               -0.30920035, -0.31596854, -0.92116749,  0.51336122,
  //               0.22002794,  0.48599416,  0.69166088,  0.85755372
  VLOAD_32(v4, 0x00000000, 0x3dcb7174, 0xbeb162ab, 0xbd7edebf, 0x3f75db3c, 0xbf4f6872, 0xbf3180f6, 0x3f3464fe,
           0xbe9e4f82, 0xbea1c6a1, 0xbf6bd1a2, 0x3f036ba4, 0x3e614f01, 0x3ef8d43a, 0x3f3110b0, 0x3f5d88a4);
  //               0x00000000, -0.64782482,  0.39402914, -0.81853813,
  //               0.24656086, -0.71423489, -0.44735566, -0.25510681,
  //               -0.94378990, -0.30138883,  0.19188073, -0.29310879,
  //               -0.22981364, -0.58626360, -0.80913633,  0.85755372
  VLOAD_32(v6, 0x00000000, 0xbf25d7d9, 0x3ec9be30, 0xbf518bb7, 0x3e7c7a73, 0xbf36d819, 0xbee50bcd, 0xbe829d5c,
           0xbf719c37, 0xbe9a4fa3, 0x3e447c62, 0xbe96125b, 0xbe6b5444, 0xbf16155f, 0xbf4f238f, 0x3f5d88a4);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vmset.m v2");
  asm volatile("vmflt.vv v2, v4, v6, v0.t");
  VSET(1, e16, m1);
  VCMP_U16(5, v2, 0x5775);
};

// Simple random test with similar values (vector-scalar)
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                             -0.2649
  BOX_HALF_IN_FLOAT(fscalar_16, 0xb43d);
  //              -0.0651,  0.5806,  0.2563, -0.4783,  0.7393, -0.2649, -0.4590,
  //              0.5469, -0.9082,  0.6235, -0.8276, -0.7939, -0.0236, -0.1166,
  //              0.4026,  0.0022
  VLOAD_16(v2, 0xac2a, 0x38a5, 0x341a, 0xb7a7, 0x39ea, 0xb43d, 0xb758, 0x3860, 0xbb44, 0x38fd, 0xba9f, 0xba5a, 0xa60b,
           0xaf76, 0x3671, 0x1896);
  asm volatile("vmset.m v1");
  asm volatile("vmflt.vf v1, v2, %[A]" ::[A] "f"(fscalar_16));
  VSET(1, e16, m1);
  VCMP_U16(7, v1, 0x0d48);

  VSET(16, e32, m2);
  float fscalar_32;
  //                               0.80517912
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0x3f4e2038);
  //              -0.15601152, -0.92020410, -0.29387674,  0.98594254,
  //              0.88163614, -0.44641387,  0.88191622,  0.15161350,
  //              -0.79952192, -0.03668820, -0.38464722, -0.54745716,
  //              0.09956384,  0.21655059, -0.37557366, -0.79342169
  VLOAD_32(v4, 0xbe1fc17c, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038,
           0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0x3f4e2038, 0xbf4b1daf);
  asm volatile("vmset.m v2");
  asm volatile("vmflt.vf v2, v4, %[A]" ::[A] "f"(fscalar_32));
  VSET(1, e16, m1);
  VCMP_U16(8, v2, 0x8001);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                             -0.2649
  BOX_HALF_IN_FLOAT(fscalar_16, 0xb43d);
  //               -0.2649,  0.5806, -0.2649, -0.4783, -0.2649, -0.2649,
  //               -0.2649, -0.2649, -0.2649, -0.2649, -0.2649, -0.2649,
  //               -0.2649, -0.2649, -0.2649, -0.2649,
  VLOAD_16(v2, 0xb43d, 0x7653, 0xad3d, 0x033d, 0xb43d, 0xb43d, 0xb43d, 0xb43d, 0xb43d, 0xb43d, 0xb43d, 0xb43d, 0xb43d,
           0xb43d, 0xb43d, 0xb43d);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vmset.m v1");
  asm volatile("vmflt.vf v1, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  VSET(1, e16, m1);
  VCMP_U16(10, v1, 0x5555);

  VSET(16, e32, m2);
  float fscalar_32;
  //                               0.80517912
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0x3f4e2038);
  //                0.80517912,  0.80517912, -0.29387674,  0.98594254,
  //                0.88163614, -0.44641387,  0.88191622,  0.15161350,
  //                -0.79952192, -0.03668820, -0.38464722, -0.54745716,
  //                0.09956384,  0.21655059, -0.37557366, -0.79342169
  VLOAD_32(v4, 0x3f4e2038, 0x3f4e2038, 0xbe967703, 0x3f7c66bb, 0x3f61b2e8, 0xbee4905c, 0x3f61c543, 0x3e1b4092,
           0xbf4cad78, 0xbd16465d, 0xbec4f07b, 0xbf0c2627, 0x3dcbe820, 0x3e5dbf70, 0xbec04b31, 0xbf4b1daf);
  VLOAD_8(v0, 0xAA, 0xAA);
  asm volatile("vmset.m v2");
  asm volatile("vmflt.vf v2, v4, %[A], v0.t" ::[A] "f"(fscalar_32));
  VSET(1, e16, m1);
  VCMP_U16(11, v2, 0xfff5);
};

int main(void) {
  INIT_CHECK();
  enable_vec();
  enable_fp();

  VSET(1, e16, m1);
  VCLEAR(v0);
  VCLEAR(v1);
  VCLEAR(v2);
  VCLEAR(v3);

  TEST_CASE1();
  MASKED_TEST(TEST_CASE2());
  TEST_CASE3();
  MASKED_TEST(TEST_CASE4());

  EXIT_CHECK();
}
