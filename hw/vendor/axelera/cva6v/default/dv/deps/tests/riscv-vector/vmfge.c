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
  //                             -0.2649
  BOX_HALF_IN_FLOAT(fscalar_16, 0xb43d);
  //              -0.0651,  0.5806,  0.2563, -0.4783,  0.7393, -0.2649, -0.4590,
  //              0.5469, -0.9082,  0.6235, -0.8276, -0.7939, -0.0236, -0.1166,
  //              0.4026,  0.0022
  VLOAD_16(v2, 0xac2a, 0x38a5, 0x341a, 0xb7a7, 0x39ea, 0xb43d, 0xb758, 0x3860, 0xbb44, 0x38fd, 0xba9f, 0xba5a, 0xa60b,
           0xaf76, 0x3671, 0x1896);
  asm volatile("vmset.m v1");
  asm volatile("vmfge.vf v1, v2, %[A]" ::[A] "f"(fscalar_16));
  VSET(1, e16, m1);
  VCMP_U16(1, v1, 0xf2b7);

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
  asm volatile("vmfge.vf v2, v4, %[A]" ::[A] "f"(fscalar_32));
  VSET(1, e16, m1);
  VCMP_U16(2, v2, 0x7ffe);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE2(void) {
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
  asm volatile("vmfge.vf v1, v2, %[A], v0.t" ::[A] "f"(fscalar_16));
  VSET(1, e16, m1);
  VCMP_U16(4, v1, 0xffff);

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
  asm volatile("vmfge.vf v2, v4, %[A], v0.t" ::[A] "f"(fscalar_32));
  VSET(1, e16, m1);
  VCMP_U16(5, v2, 0x555f);
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

  EXIT_CHECK();
}
