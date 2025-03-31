// Description: This test application demonstrates the functionality of RISC-V vector extensions by performing
// and validating vectorized addition operations on arrays of different data types, including 8-bit integers,
// 16-bit integers, 32-bit floats, and 16-bit half-precision floats. It employs a stripmining loop to handle
// vector operations efficiently, verifies correct calculations by comparing results against expected values,
// and checks for proper floating-point exception handling.
//
// The test initializes arrays for each data type, performs vectorized addition and validates the results.
// The final message confirms the correct functioning of RISC-V vector operations.

#include <riscv_vector.h>
#include <stdint.h>
#include <testutils.h>
#include <printf.h>

#define VL 40

int8_t __attribute__((aligned(64), section(".l1")))
A[VL] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
         0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
int8_t __attribute__((aligned(64), section(".l1")))
B[VL] = {9, 0, 8, 1, 7, 2, 6, 3, 5, 4, 9, 0, 8, 1, 7, 2, 6, 3, 5, 4,
         9, 0, 8, 1, 7, 2, 6, 3, 5, 4, 9, 0, 8, 1, 7, 2, 6, 3, 5, 4};
int8_t __attribute__((aligned(64), section(".l1"))) C[VL];

int16_t __attribute__((aligned(64), section(".l1")))
Ah[VL] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
          0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
int16_t __attribute__((aligned(64), section(".l1")))
Bh[VL] = {9, 0, 8, 1, 7, 2, 6, 3, 5, 4, 9, 0, 8, 1, 7, 2, 6, 3, 5, 4,
          9, 0, 8, 1, 7, 2, 6, 3, 5, 4, 9, 0, 8, 1, 7, 2, 6, 3, 5, 4};
int16_t __attribute__((aligned(64), section(".l1"))) Ch[VL];

float __attribute__((aligned(64), section(".l1"))) Af[VL] = {
    0.0,     1.8, 202.5, 3425.123, 4.0,   51.2463, 6.9, 7.1,   8.0001,   9.985, 0.0,     1.8, 202.5, 3425.123, 4.0,
    51.2463, 6.9, 7.1,   8.0001,   9.985, 0.0,     1.8, 202.5, 3425.123, 4.0,   51.2463, 6.9, 7.1,   8.0001,   9.985,
    0.0,     1.8, 202.5, 3425.123, 4.0,   51.2463, 6.9, 7.1,   8.0001,   9.985};
float __attribute__((aligned(64), section(".l1"))) Bf[VL] = {
    9.985,    0.0,    1.8,     202.5, 3425.123, 4.0,    51.2463,  6.9, 7.1,     8.0001, 9.985,    0.0,   1.8,     202.5,
    3425.123, 4.0,    51.2463, 6.9,   7.1,      8.0001, 9.985,    0.0, 1.8,     202.5,  3425.123, 4.0,   51.2463, 6.9,
    7.1,      8.0001, 9.985,   0.0,   1.8,      202.5,  3425.123, 4.0, 51.2463, 6.9,    7.1,      8.0001};
float __attribute__((aligned(64), section(".l1"))) Cf[VL];

_Float16 __attribute__((aligned(64), section(".l1"))) Afh[VL] = {
    0.0,     1.8, 202.5, 3425.123, 4.0,   51.2463, 6.9, 7.1,   8.0001,   9.985, 0.0,     1.8, 202.5, 3425.123, 4.0,
    51.2463, 6.9, 7.1,   8.0001,   9.985, 0.0,     1.8, 202.5, 3425.123, 4.0,   51.2463, 6.9, 7.1,   8.0001,   9.985,
    0.0,     1.8, 202.5, 3425.123, 4.0,   51.2463, 6.9, 7.1,   8.0001,   9.985};
_Float16 __attribute__((aligned(64), section(".l1"))) Bfh[VL] = {
    9.985,    0.0,    1.8,     202.5, 3425.123, 4.0,    51.2463,  6.9, 7.1,     8.0001, 9.985,    0.0,   1.8,     202.5,
    3425.123, 4.0,    51.2463, 6.9,   7.1,      8.0001, 9.985,    0.0, 1.8,     202.5,  3425.123, 4.0,   51.2463, 6.9,
    7.1,      8.0001, 9.985,   0.0,   1.8,      202.5,  3425.123, 4.0, 51.2463, 6.9,    7.1,      8.0001};
_Float16 __attribute__((aligned(64), section(".l1"))) Cfh[VL];

// vfloat16m1_t vAfh;

int main() {
  int _8_int_error = 1;
  int _16_int_error = 1;
  int _32_float_error = 1;
  int _16_float_error = 1;

  testcase_init();
  printf("Running stripmining loop...\n");

  // Vector integer stripmining loop
  uint32_t remaining_elem = VL;
  int8_t  *ptr_vec_A      = A;
  int8_t  *ptr_vec_B      = B;
  int8_t  *ptr_vec_C      = C;
  while (remaining_elem > 0) {
    uint32_t  vl;
    vint8m1_t vA, vB, vC;
    vl = __riscv_vsetvl_e8m1(remaining_elem);
    vA = __riscv_vle8_v_i8m1(ptr_vec_A, vl);
    vB = __riscv_vle8_v_i8m1(ptr_vec_B, vl);
    vC = __riscv_vadd_vv_i8m1(vA, vB, vl);
    __riscv_vse8_v_i8m1(ptr_vec_C, vC, vl);
    remaining_elem -= vl;
    ptr_vec_A      += vl;
    ptr_vec_B      += vl;
    ptr_vec_C      += vl;
  }
  // Check for correct calculation
  for (int i = 0; i < VL; i++) {
    if (A[i] + B[i] != C[i]){
      _8_int_error = 0;
      break;
    }
  }
  CHECK_TRUE(_8_int_error, "8-bit integers not supported!");

  // Vector integer stripmining loop
  remaining_elem      = VL;
  int16_t *ptr_vec_Ah = Ah;
  int16_t *ptr_vec_Bh = Bh;
  int16_t *ptr_vec_Ch = Ch;
  while (remaining_elem > 0) {
    uint32_t   vl;
    vint16m1_t vAh, vBh, vCh;
    vl  = __riscv_vsetvl_e16m1(remaining_elem);
    vAh = __riscv_vle16_v_i16m1(ptr_vec_Ah, vl);
    vBh = __riscv_vle16_v_i16m1(ptr_vec_Bh, vl);
    vCh = __riscv_vadd_vv_i16m1(vAh, vBh, vl);
    __riscv_vse16_v_i16m1(ptr_vec_Ch, vCh, vl);
    remaining_elem -= vl;
    ptr_vec_Ah     += vl;
    ptr_vec_Bh     += vl;
    ptr_vec_Ch     += vl;
  }
  // Check for correct calculation
  for (int i = 0; i < VL; i++) {
    if (Ah[i] + Bh[i] != Ch[i]) {
      _16_int_error = 0;
      break;
    }
  }
  CHECK_TRUE(_16_int_error, "16-bit integers not supported!");

  // Vector float stripmining loop
  remaining_elem    = VL;
  float *ptr_vec_Af = Af;
  float *ptr_vec_Bf = Bf;
  float *ptr_vec_Cf = Cf;
  int    fflags     = 0;
  asm volatile("csrwi fflags, 0");
  while (remaining_elem > 0) {
    uint32_t     vl;
    vfloat32m1_t vAf, vBf, vCf;
    vl  = __riscv_vsetvl_e32m1(remaining_elem);
    vAf = __riscv_vle32_v_f32m1(ptr_vec_Af, vl);
    vBf = __riscv_vle32_v_f32m1(ptr_vec_Bf, vl);
    vCf = __riscv_vfadd_vv_f32m1(vAf, vBf, vl);
    int _fflags;
    asm volatile("csrr %0, fflags" : "=r"(_fflags));
    fflags |= _fflags;
    __riscv_vse32_v_f32m1(ptr_vec_Cf, vCf, vl);
    remaining_elem -= vl;
    ptr_vec_Af     += vl;
    ptr_vec_Bf     += vl;
    ptr_vec_Cf     += vl;
  }
  if (fflags != 0x1) {
    printf("Error: expected fflags=0x1 (but got 0x%x)\n", fflags);
    return -1;
  }
  // Check for correct calculation
  for (int i = 0; i < VL; i++) {
    if (Af[i] + Bf[i] != Cf[i]) {
      _32_float_error = 0;
      break;
    }
  }
  CHECK_TRUE(_32_float_error, "Single precision floats not supported!");

  // Vector float stripmining loop
  remaining_elem        = VL;
  _Float16 *ptr_vec_Afh = Afh;
  _Float16 *ptr_vec_Bfh = Bfh;
  _Float16 *ptr_vec_Cfh = Cfh;
  while (remaining_elem > 0) {
    uint32_t     vl;
    vfloat16m1_t vAfh, vBfh, vCfh;
    vl   = __riscv_vsetvl_e16m1(remaining_elem);
    vAfh = __riscv_vle16_v_f16m1(ptr_vec_Afh, vl);
    vBfh = __riscv_vle16_v_f16m1(ptr_vec_Bfh, vl);
    vCfh = __riscv_vfadd_vv_f16m1(vAfh, vBfh, vl);
    __riscv_vse16_v_f16m1(ptr_vec_Cfh, vCfh, vl);
    remaining_elem -= vl;
    ptr_vec_Afh    += vl;
    ptr_vec_Bfh    += vl;
    ptr_vec_Cfh    += vl;
  }
  // Check for correct calculation
  for (int i = 0; i < VL; i++) {
    if (Afh[i] + Bfh[i] != Cfh[i]) {
      _16_float_error = 0;
      break;
    }
  }
  CHECK_TRUE(_16_float_error, "Half precision floats not supported!");


  if (_8_int_error && _16_int_error && _32_float_error && _16_float_error){
    printf("... 8-bit integers are supported\n");
    printf("... 16-bit integers are supported\n");
    printf("... floats are supported\n");
    printf("... half precision floats are supported\n");
    printf("RISC-V vectors are working properly!\n");
  }
  else{
    printf("RISC-V vectors are not working properly!\n");
  }

  return testcase_finalize();
}
