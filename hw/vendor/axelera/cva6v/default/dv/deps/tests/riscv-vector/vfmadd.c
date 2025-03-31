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
  //               0.3501, -0.3289, -0.8853, -0.4082, -0.4346, -0.2659,  0.9316,
  //               0.5444, -0.0538,  0.7686,  0.8203, -0.8623,  0.3059,  0.0372,
  //               0.5337, -0.5815
  VLOAD_16(v2, 0x359a, 0xb543, 0xbb15, 0xb688, 0xb6f4, 0xb441, 0x3b74, 0x385b, 0xaae4, 0x3a26, 0x3a90, 0xbae6, 0x34e5,
           0x28c4, 0x3845, 0xb8a7);
  //              -0.8105,  0.5000, -0.8374, -0.8394,  0.3098,  0.1328, -0.2864,
  //              -0.4041, -0.1729,  0.0196,  0.2739,  0.8071, -0.1553,  0.2815,
  //              -0.9067, -0.2495
  VLOAD_16(v3, 0xba7c, 0x3800, 0xbab3, 0xbab7, 0x34f5, 0x3040, 0xb495, 0xb677, 0xb188, 0x2502, 0x3462, 0x3a75, 0xb0f8,
           0x3481, 0xbb41, 0xb3fc);
  //              -0.6558, -0.1006,  0.4558, -0.0784,  0.1539,  0.6748,  0.3347,
  //              -0.3416,  0.0614,  0.2289, -0.0829,  0.3838, -0.6348,  0.0843,
  //              -0.6890, -0.2598
  VLOAD_16(v1, 0xb93f, 0xae71, 0x374b, 0xad05, 0x30ed, 0x3966, 0x355b, 0xb577, 0x2bdc, 0x3353, 0xad4f, 0x3624, 0xb914,
           0x2d65, 0xb983, 0xb428);
  asm volatile("vfmadd.vv v1, v2, v3");
  //              -1.0400,  0.5332, -1.2412, -0.8071,  0.2429, -0.0466,  0.0254,
  //              -0.5898, -0.1761,  0.1954,  0.2058,  0.4761, -0.3496,  0.2847,
  //              -1.2744, -0.0984
  VCMP_U16(1, v1, 0xbc29, 0x3844, 0xbcf7, 0xba75, 0x33c6, 0xa9f7, 0x2684, 0xb8b8, 0xb1a3, 0x3241, 0x3297, 0x379e,
           0xb597, 0x348e, 0xbd19, 0xae4d);

  VSET(16, e32, m2);
  //              -0.20637949, -0.63321692,  0.40850523,  0.58702314,
  //              -0.25534528, -0.22053087,  0.96057665,  0.85530519,
  //              0.74252450, -0.87175107, -0.00987994, -0.52556008, 0.26113954,
  //              -0.71307814,  0.78942811,  0.48685852
  VLOAD_32(v4, 0xbe535525, 0xbf221a81, 0x3ed12799, 0x3f164726, 0xbe82bc9e, 0xbe61d2d8, 0x3f75e85a, 0x3f5af548,
           0x3f3e1616, 0xbf5f2b14, 0xbc21df78, 0xbf068b1b, 0x3e85b415, 0xbf368c4a, 0x3f4a17f6, 0x3ef94585);
  //              -0.15712014,  0.83088422,  0.57509524,  0.85365236,
  //              -0.96695948,  0.71368766,  0.23281342, -0.67807233,
  //              0.79363507,  0.62817359,  0.37205252,  0.27726358,
  //              -0.85021532, -0.16634122, -0.58148408,  0.06963744
  VLOAD_32(v6, 0xbe20e41a, 0x3f54b4d4, 0x3f133971, 0x3f5a88f6, 0xbf778aa8, 0x3f36b43c, 0x3e6e66a4, 0xbf2d9626,
           0x3f4b2bab, 0x3f20cffc, 0x3ebe7dab, 0x3e8df57e, 0xbf59a7b6, 0xbe2a555a, 0xbf14dc24, 0x3d8e9e13);
  //              -0.63061494,  0.57643133,  0.08198822, -0.06029604,
  //              -0.84276563,  0.00681775,  0.30881208,  0.27571887,
  //              0.12349209,  0.29805747, -0.55497122, -0.52685922, 0.82809180,
  //              -0.83231467,  0.20959182,  0.15603130
  VLOAD_32(v2, 0xbf216ffb, 0x3f139101, 0x3da7e970, 0xbd76f8fa, 0xbf57bf7d, 0x3bdf676d, 0x3e9e1c9e, 0x3e8d2b06,
           0x3dfce96c, 0x3e989afd, 0xbf0e1298, 0xbf06e03f, 0x3f53fdd3, 0xbf551293, 0x3e569f3d, 0x3e1fc6ab);
  asm volatile("vfmadd.vv v2, v4, v6");
  //              -0.02697416,  0.46587816,  0.60858786,  0.81825721,
  //              -0.75176322,  0.71218413,  0.52945113, -0.44224855,
  //              0.88533098,  0.36834168,  0.37753561,  0.55415976,
  //              -0.63396782,  0.42716417, -0.41602641,  0.14560261
  VCMP_U32(2, v2, 0xbcdcf8e5, 0x3eee8795, 0x3f1bcc6a, 0x3f51794e, 0xbf40738e, 0x3f3651b3, 0x3f078a1b, 0xbee26e67,
           0x3f62a50d, 0x3ebc9748, 0x3ec14c59, 0x3f0ddd6a, 0xbf224bb7, 0x3edab544, 0xbed5016a, 0x3e1518d9);
};

// Simple random test with similar values + 1 subnormal (masked)
// The numbers are the same of TEST_CASE1
void TEST_CASE2(void) {
  VSET(16, e16, m1);
  //               0.3501, -0.3289, -0.8853, -0.4082, -0.4346, -0.2659,  0.9316,
  //               0.5444, -0.0538,  0.7686,  0.8203, -0.8623,  0.3059,  0.0372,
  //               0.5337, -0.5815
  VLOAD_16(v2, 0x359a, 0xb543, 0xbb15, 0xb688, 0xb6f4, 0xb441, 0x3b74, 0x385b, 0xaae4, 0x3a26, 0x3a90, 0xbae6, 0x34e5,
           0x28c4, 0x3845, 0xb8a7);
  //              -0.8105,  0.5000, -0.8374, -0.8394,  0.3098,  0.1328, -0.2864,
  //              -0.4041, -0.1729,  0.0196,  0.2739,  0.8071, -0.1553,  0.2815,
  //              -0.9067, -0.2495
  VLOAD_16(v3, 0xba7c, 0x3800, 0xbab3, 0xbab7, 0x34f5, 0x3040, 0xb495, 0xb677, 0xb188, 0x2502, 0x3462, 0x3a75, 0xb0f8,
           0x3481, 0xbb41, 0xb3fc);
  VLOAD_8(v0, 0xAA, 0xAA);
  //              -0.6558, -0.1006,  0.4558, -0.0784,  0.1539,  0.6748,  0.3347,
  //              -0.3416,  0.0614,  0.2289, -0.0829,  0.3838, -0.6348,  0.0843,
  //              -0.6890, -0.2598
  VLOAD_16(v1, 0xb93f, 0xae71, 0x374b, 0xad05, 0x30ed, 0x3966, 0x355b, 0xb577, 0x2bdc, 0x3353, 0xad4f, 0x3624, 0xb914,
           0x2d65, 0xb983, 0xb428);
  asm volatile("vfmadd.vv v1, v2, v3, v0.t");
  VCMP_U16(4, v1, 0xb93f, 0x3844, 0x374b, 0xba75, 0x30ed, 0xa9f7, 0x355b, 0xb8b8, 0x2bdc, 0x3241, 0xad4f, 0x379e,
           0xb914, 0x348e, 0xb983, 0xae4d);

  VSET(16, e32, m2);
  //              -0.20637949, -0.63321692,  0.40850523,  0.58702314,
  //              -0.25534528, -0.22053087,  0.96057665,  0.85530519,
  //              0.74252450, -0.87175107, -0.00987994, -0.52556008, 0.26113954,
  //              -0.71307814,  0.78942811,  0.48685852
  VLOAD_32(v4, 0xbe535525, 0xbf221a81, 0x3ed12799, 0x3f164726, 0xbe82bc9e, 0xbe61d2d8, 0x3f75e85a, 0x3f5af548,
           0x3f3e1616, 0xbf5f2b14, 0xbc21df78, 0xbf068b1b, 0x3e85b415, 0xbf368c4a, 0x3f4a17f6, 0x3ef94585);
  //              -0.15712014,  0.83088422,  0.57509524,  0.85365236,
  //              -0.96695948,  0.71368766,  0.23281342, -0.67807233,
  //              0.79363507,  0.62817359,  0.37205252,  0.27726358,
  //              -0.85021532, -0.16634122, -0.58148408,  0.06963744
  VLOAD_32(v6, 0xbe20e41a, 0x3f54b4d4, 0x3f133971, 0x3f5a88f6, 0xbf778aa8, 0x3f36b43c, 0x3e6e66a4, 0xbf2d9626,
           0x3f4b2bab, 0x3f20cffc, 0x3ebe7dab, 0x3e8df57e, 0xbf59a7b6, 0xbe2a555a, 0xbf14dc24, 0x3d8e9e13);
  VLOAD_8(v0, 0xAA, 0xAA);
  //              -0.63061494,  0.57643133,  0.08198822, -0.06029604,
  //              -0.84276563,  0.00681775,  0.30881208,  0.27571887,
  //              0.12349209,  0.29805747, -0.55497122, -0.52685922, 0.82809180,
  //              -0.83231467,  0.20959182,  0.15603130
  VLOAD_32(v2, 0xbf216ffb, 0x3f139101, 0x3da7e970, 0xbd76f8fa, 0xbf57bf7d, 0x3bdf676d, 0x3e9e1c9e, 0x3e8d2b06,
           0x3dfce96c, 0x3e989afd, 0xbf0e1298, 0xbf06e03f, 0x3f53fdd3, 0xbf551293, 0x3e569f3d, 0x3e1fc6ab);
  asm volatile("vfmadd.vv v2, v4, v6, v0.t");
  VCMP_U32(5, v2, 0xbf216ffb, 0x3eee8795, 0x3da7e970, 0x3f51794e, 0xbf57bf7d, 0x3f3651b3, 0x3e9e1c9e, 0xbee26e67,
           0x3dfce96c, 0x3ebc9748, 0xbf0e1298, 0x3f0ddd6a, 0x3f53fdd3, 0x3edab544, 0x3e569f3d, 0x3e1518d9);
};

// Simple random test with similar values (vector-scalar)
void TEST_CASE3(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                              0.6299
  BOX_HALF_IN_FLOAT(fscalar_16, 0x390a);
  //              -0.5352,  0.1115,  0.9541, -0.8857, -0.4143,  0.4045,  0.2949,
  //              -0.5479,  0.6733,  0.8965,  0.8882,  0.6294,  0.7568,  0.8735,
  //              -0.8569,  0.8271
  VLOAD_16(v2, 0xb848, 0x2f23, 0x3ba2, 0xbb16, 0xb6a1, 0x3679, 0x34b8, 0xb862, 0x3963, 0x3b2c, 0x3b1b, 0x3909, 0x3a0e,
           0x3afd, 0xbadb, 0x3a9e);
  //               0.2844,  0.1008,  0.3777,  0.9790, -0.8613,  0.4951,  0.4126,
  //               0.5518, -0.6680, -0.8340,  0.2094,  0.5884, -0.6509, -0.9360,
  //               -0.1609, -0.2527
  VLOAD_16(v1, 0x348d, 0x2e74, 0x360b, 0x3bd5, 0xbae4, 0x37ec, 0x369a, 0x386a, 0xb958, 0xbaac, 0x32b3, 0x38b5, 0xb935,
           0xbb7d, 0xb126, 0xb40b);
  asm volatile("vfmadd.vf v1, %[A], v2" ::[A] "f"(fscalar_16));
  //              -0.3560,  0.1750,  1.1924, -0.2690, -0.9570,  0.7163,  0.5547,
  //              -0.2002,  0.2527,  0.3711,  1.0195,  1.0000,  0.3469,  0.2842,
  //              -0.9580,  0.6680
  VCMP_U16(7, v1, 0xb5b2, 0x319a, 0x3cc5, 0xb44e, 0xbba8, 0x39bb, 0x3870, 0xb269, 0x340b, 0x35f0, 0x3c15, 0x3c00,
           0x358d, 0x348b, 0xbbab, 0x3958);

  VSET(16, e32, m2);
  float fscalar_32;
  //                               0.80368215
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0x3f4dbe1d);
  //               0.13072050, -0.19741143,  0.09370349,  0.41049519,
  //               -0.69910282, -0.90573430,  0.86481184,  0.33341369,
  //               0.30657578, -0.90526944, -0.97891974, -0.50830764,
  //               0.79750061,  0.96885878,  0.48752418,  0.64305341
  VLOAD_32(v4, 0x3e05db98, 0xbe4a2639, 0x3dbfe79e, 0x3ed22c6d, 0xbf32f867, 0xbf67de34, 0x3f5d644f, 0x3eaab533,
           0x3e9cf780, 0xbf67bfbd, 0xbf7a9a7c, 0xbf022073, 0x3f4c2900, 0x3f780721, 0x3ef99cc5, 0x3f249f26);
  //              -0.61117887,  0.81778014, -0.46267223, -0.30897874,
  //              -0.84296966,  0.50125730,  0.96147668,  0.65802389,
  //              0.19629262, -0.73197508, -0.06948850, -0.60436314,
  //              -0.80817568,  0.72047287, -0.78180677, -0.40237895
  VLOAD_32(v2, 0xbf1c7638, 0x3f515a0a, 0xbeece360, 0xbe9e3276, 0xbf57ccdc, 0x3f005266, 0x3f762356, 0x3f287441,
           0x3e4900ef, 0xbf3b62b8, 0xbd8e4ffc, 0xbf1ab78b, 0xbf4ee49a, 0x3f3870e9, 0xbf48247d, 0xbece049d);
  asm volatile("vfmadd.vf v2, %[A], v4" ::[A] "f"(fscalar_32));
  //              -0.36047307,  0.45982391, -0.27813792,  0.16217449,
  //              -1.37658250, -0.50288272,  1.63753343,  0.86225569,
  //              0.46433264, -1.49354482, -1.03476644, -0.99402350, 0.14798427,
  //              1.54788995, -0.14079997,  0.31966865
  VCMP_U32(8, v2, 0xbeb88fed, 0x3eeb6e09, 0xbe8e6818, 0x3e261112, 0xbfb033db, 0xbf00bced, 0x3fd19ab2, 0x3f5cbccb,
           0x3eedbd02, 0xbfbf2c79, 0xbf84733a, 0xbf7e7853, 0x3e17892e, 0x3fc62142, 0xbe102ddd, 0x3ea3ab9c);
};

// Simple random test with similar values (vector-scalar) (masked)
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  float fscalar_16;
  //                              0.6299
  BOX_HALF_IN_FLOAT(fscalar_16, 0x390a);
  //               -0.5352,  0.1115,  0.9541, -0.8857, -0.4143,  0.4045, 0.2949,
  //               -0.5479,  0.6733,  0.8965,  0.8882,  0.6294,  0.7568, 0.8735,
  //               -0.8569,  0.8271
  VLOAD_16(v2, 0xb848, 0x2f23, 0x3ba2, 0xbb16, 0xb6a1, 0x3679, 0x34b8, 0xb862, 0x3963, 0x3b2c, 0x3b1b, 0x3909, 0x3a0e,
           0x3afd, 0xbadb, 0x3a9e);
  VLOAD_8(v0, 0xAA, 0xAA);
  //                0.2844,  0.1008,  0.3777,  0.9790, -0.8613,  0.4951, 0.4126,
  //                0.5518, -0.6680, -0.8340,  0.2094,  0.5884, -0.6509,
  //                -0.9360, -0.1609, -0.2527
  VLOAD_16(v1, 0x348d, 0x2e74, 0x360b, 0x3bd5, 0xbae4, 0x37ec, 0x369a, 0x386a, 0xb958, 0xbaac, 0x32b3, 0x38b5, 0xb935,
           0xbb7d, 0xb126, 0xb40b);
  asm volatile("vfmadd.vf v1, %[A], v2, v0.t" ::[A] "f"(fscalar_16));
  VCMP_U16(10, v1, 0x348d, 0x319a, 0x360b, 0xb44e, 0xbae4, 0x39bb, 0x369a, 0xb269, 0xb958, 0x35f0, 0x32b3, 0x3c00,
           0xb935, 0x348b, 0xb126, 0x3958);

  VSET(16, e32, m2);
  float fscalar_32;
  //                               0.80368215
  BOX_FLOAT_IN_FLOAT(fscalar_32, 0x3f4dbe1d);
  //                0.13072050, -0.19741143,  0.09370349,  0.41049519,
  //                -0.69910282, -0.90573430,  0.86481184,  0.33341369,
  //                0.30657578, -0.90526944, -0.97891974, -0.50830764,
  //                0.79750061,  0.96885878,  0.48752418,  0.64305341
  VLOAD_32(v4, 0x3e05db98, 0xbe4a2639, 0x3dbfe79e, 0x3ed22c6d, 0xbf32f867, 0xbf67de34, 0x3f5d644f, 0x3eaab533,
           0x3e9cf780, 0xbf67bfbd, 0xbf7a9a7c, 0xbf022073, 0x3f4c2900, 0x3f780721, 0x3ef99cc5, 0x3f249f26);
  VLOAD_8(v0, 0xAA, 0xAA);
  //               -0.61117887,  0.81778014, -0.46267223, -0.30897874,
  //               -0.84296966,  0.50125730,  0.96147668,  0.65802389,
  //               0.19629262, -0.73197508, -0.06948850, -0.60436314,
  //               -0.80817568,  0.72047287, -0.78180677, -0.40237895
  VLOAD_32(v2, 0xbf1c7638, 0x3f515a0a, 0xbeece360, 0xbe9e3276, 0xbf57ccdc, 0x3f005266, 0x3f762356, 0x3f287441,
           0x3e4900ef, 0xbf3b62b8, 0xbd8e4ffc, 0xbf1ab78b, 0xbf4ee49a, 0x3f3870e9, 0xbf48247d, 0xbece049d);
  asm volatile("vfmadd.vf v2, %[A], v4, v0.t" ::[A] "f"(fscalar_32));
  VCMP_U32(11, v2, 0xbf1c7638, 0x3eeb6e09, 0xbeece360, 0x3e261112, 0xbf57ccdc, 0xbf00bced, 0x3f762356, 0x3f5cbccb,
           0x3e4900ef, 0xbfbf2c79, 0xbd8e4ffc, 0xbf7e7853, 0xbf4ee49a, 0x3fc62142, 0xbf48247d, 0x3ea3ab9c);
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
