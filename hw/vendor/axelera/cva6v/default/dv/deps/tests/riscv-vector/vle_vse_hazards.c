#include "vector_macros.h"

#define AXI_DWIDTH 128

#define INIT 98

void reset_vec8(volatile uint8_t *vec, int rst_val, uint64_t len) {
  for (uint64_t i = 0; i < len; ++i) vec[i] = rst_val;
}
void reset_vec16(volatile uint16_t *vec, int rst_val, uint64_t len) {
  for (uint64_t i = 0; i < len; ++i) vec[i] = rst_val;
}
void reset_vec32(volatile uint32_t *vec, int rst_val, uint64_t len) {
  for (uint64_t i = 0; i < len; ++i) vec[i] = rst_val;
}

static volatile uint8_t TEST_I8[16]
    __attribute__((aligned(AXI_DWIDTH))) = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
static volatile uint16_t TEST_I16[16]
    __attribute__((aligned(AXI_DWIDTH))) = {2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32};
static volatile uint32_t TEST_I32[16]
    __attribute__((aligned(AXI_DWIDTH))) = {4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64};

static volatile uint8_t ALIGNED_I8[16] __attribute__((aligned(AXI_DWIDTH))) = {
    0xe0, 0xd3, 0x40, 0xd1, 0x84, 0x48, 0x89, 0x88, 0x88, 0xae, 0x08, 0x91, 0x02, 0x59, 0x11, 0x89};
static volatile uint16_t ALIGNED_I16[16]
    __attribute__((aligned(AXI_DWIDTH))) = {0x05e0, 0xbbd3, 0x3840, 0x8cd1, 0x9384, 0x7548, 0x3489, 0x9388,
                                            0x8188, 0x11ae, 0x5808, 0x4891, 0x4902, 0x8759, 0x1111, 0x1989};
static volatile uint32_t ALIGNED_I32[16] __attribute__((aligned(AXI_DWIDTH))) = {
    0x9fe41920, 0xf9aa71f0, 0xa11a9384, 0x99991348, 0x9fa831c7, 0x38197598, 0x18931795, 0x81937598,
    0x18747547, 0x3eeeeeee, 0x90139301, 0xab8b9148, 0x90318509, 0x31897598, 0x83195999, 0x89139848};

static volatile uint8_t BUFFER_O8[16] __attribute__((aligned(AXI_DWIDTH))) = {
    INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT};
static volatile uint16_t BUFFER_O16[16] __attribute__((aligned(AXI_DWIDTH))) = {
    INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT};
static volatile uint32_t BUFFER_O32[16] __attribute__((aligned(AXI_DWIDTH))) = {
    INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT, INIT};

//****** RAW Hazard****//
void TEST_CASE1(void) {
  VSET(16, e8, m1);
  asm volatile("vle8.v v1, (%0)" ::"r"(&ALIGNED_I8[0]));
  asm volatile("vse8.v v1, (%0)" ::"r"(&BUFFER_O8[0]));
  VVCMP_U8(1, BUFFER_O8, 0xe0, 0xd3, 0x40, 0xd1, 0x84, 0x48, 0x89, 0x88, 0x88, 0xae, 0x08, 0x91, 0x02, 0x59, 0x11,
           0x89);
}

//******WAR Hazard****//
void TEST_CASE2(void) {
  reset_vec8(&BUFFER_O8[0], INIT, 16);
  VSET(16, e8, m1);
  VLOAD_8(v2, 0xe0, 0xd3, 0x40, 0xd1, 0x84, 0x48, 0x89, 0x88, 0x88, 0xae, 0x08, 0x91, 0x02, 0x59, 0x11, 0x89);
  asm volatile("vse8.v v2, (%0)" ::"r"(&BUFFER_O8[0]));
  asm volatile("vle8.v v2, (%0)" ::"r"(&BUFFER_O8[0]));
  VCMP_U8(2, v2, 0xe0, 0xd3, 0x40, 0xd1, 0x84, 0x48, 0x89, 0x88, 0x88, 0xae, 0x08, 0x91, 0x02, 0x59, 0x11, 0x89);
}

//******WAW Hazard****//
void TEST_CASE3(void) {
  VSET(16, e8, m1);
  asm volatile("vle8.v v3, (%0)" ::"r"(&ALIGNED_I8[0]));
  asm volatile("vle8.v v3, (%0)" ::"r"(&TEST_I8[0]));
  VCMP_U8(3, v3, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
}

//****** RAW Hazard****//
void TEST_CASE4(void) {
  VSET(16, e16, m1);
  asm volatile("vle16.v v4, (%0)" ::"r"(&ALIGNED_I16[0]));
  asm volatile("vse16.v v4, (%0)" ::"r"(&BUFFER_O16[0]));
  VVCMP_U16(4, BUFFER_O16, 0x05e0, 0xbbd3, 0x3840, 0x8cd1, 0x9384, 0x7548, 0x3489, 0x9388, 0x8188, 0x11ae, 0x5808,
            0x4891, 0x4902, 0x8759, 0x1111, 0x1989);
}

//******WAR Hazard****//
void TEST_CASE5(void) {
  reset_vec16(&BUFFER_O16[0], INIT, 16);
  VSET(16, e16, m1);
  VLOAD_16(v5, 0x05e0, 0xbbd3, 0x3840, 0x8cd1, 0x9384, 0x7548, 0x3489, 0x9388, 0x8188, 0x11ae, 0x5808, 0x4891, 0x4902,
           0x8759, 0x1111, 0x1989);
  asm volatile("vse16.v v5, (%0)" ::"r"(&BUFFER_O16[0]));
  asm volatile("vle16.v v5, (%0)" ::"r"(&BUFFER_O16[0]));
  VCMP_U16(5, v5, 0x05e0, 0xbbd3, 0x3840, 0x8cd1, 0x9384, 0x7548, 0x3489, 0x9388, 0x8188, 0x11ae, 0x5808, 0x4891,
           0x4902, 0x8759, 0x1111, 0x1989);
}

//******WAW Hazard****//
void TEST_CASE6(void) {
  VSET(16, e16, m1);
  asm volatile("vle16.v v6, (%0)" ::"r"(&ALIGNED_I16[0]));
  asm volatile("vle16.v v6, (%0)" ::"r"(&TEST_I16[0]));
  VCMP_U16(6, v6, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32);
}

//****** RAW Hazard****//
void TEST_CASE7(void) {
  VSET(16, e32, m2);
  asm volatile("vle32.v v8, (%0)" ::"r"(&ALIGNED_I32[0]));
  asm volatile("vse32.v v8, (%0)" ::"r"(&BUFFER_O32[0]));
  VVCMP_U32(8, BUFFER_O32, 0x9fe41920, 0xf9aa71f0, 0xa11a9384, 0x99991348, 0x9fa831c7, 0x38197598, 0x18931795,
            0x81937598, 0x18747547, 0x3eeeeeee, 0x90139301, 0xab8b9148, 0x90318509, 0x31897598, 0x83195999, 0x89139848);
}

//******WAR Hazard****//
void TEST_CASE8(void) {
  reset_vec32(&BUFFER_O32[0], INIT, 16);
  VSET(16, e32, m2);
  VLOAD_32(v10, 0x9fe41920, 0xf9aa71f0, 0xa11a9384, 0x99991348, 0x9fa831c7, 0x38197598, 0x18931795, 0x81937598,
           0x18747547, 0x3eeeeeee, 0x90139301, 0xab8b9148, 0x90318509, 0x31897598, 0x83195999, 0x89139848);
  asm volatile("vse32.v v10, (%0)" ::"r"(&BUFFER_O32[0]));
  asm volatile("vle32.v v10, (%0)" ::"r"(&BUFFER_O32[0]));
  VCMP_U32(8, v10, 0x9fe41920, 0xf9aa71f0, 0xa11a9384, 0x99991348, 0x9fa831c7, 0x38197598, 0x18931795, 0x81937598,
           0x18747547, 0x3eeeeeee, 0x90139301, 0xab8b9148, 0x90318509, 0x31897598, 0x83195999, 0x89139848);
}

//******WAW Hazard****//
void TEST_CASE9(void) {
  VSET(16, e32, m2);
  asm volatile("vle32.v v12, (%0)" ::"r"(&ALIGNED_I32[0]));
  asm volatile("vle32.v v12, (%0)" ::"r"(&TEST_I32[0]));
  VCMP_U32(9, v12, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64);
}

int main(void) {
  INIT_CHECK();
  enable_vec();

  printf("*****Running tests of vle-vse for data hazards*****\n");
  TEST_CASE1();
  TEST_CASE2();
  TEST_CASE3();
  TEST_CASE4();
  TEST_CASE5();
  TEST_CASE6();
  TEST_CASE7();
  TEST_CASE8();
  TEST_CASE9();

  EXIT_CHECK();
}
