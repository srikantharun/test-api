// (C) Copyright Axelera AI 2025
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Bottleneck analysis test application
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#include <riscv_vector.h>

#include "testutils.h"
#include "printf.h"
#include "timer.h"

#define TEST_BUFFER_SZ  16384
#define TEST_PAYLOAD_SZ (512 * 1024)

static uint8_t __attribute__((aligned(64))) ddr_buf[TEST_BUFFER_SZ];
static uint8_t __attribute__((aligned(64), section(".l1"))) l1_buf[TEST_BUFFER_SZ];

#define CHECK_BANDWIDTH(INIT, TEST, PAYLOAD_SZ, MIN_BW, MAX_BW, DESC)                                            \
  ({                                                                                                             \
    INIT;                                                                                                        \
    unsigned long t_start = read_cycles();                                                                       \
    TEST;                                                                                                        \
    /* wait until Raptor is idle by reading vl */                                                                \
    long unsigned tmp = 0;                                                                                       \
    asm volatile("csrr %0, vl" : "=r"(tmp));                                                                     \
    unsigned long t_diff = read_cycles() - t_start;                                                              \
    float         bw     = (float)(PAYLOAD_SZ) / (float)t_diff;                                                  \
    float         util   = (bw / (float)(MAX_BW)) * (float)100.f; \
    printf("%s %d bytes in %8lu cycles => %f bytes/cycle, utilization %f %%\n", DESC, PAYLOAD_SZ, t_diff, CVA6V_PRINTF_FLOAT(bw), CVA6V_PRINTF_FLOAT(util)); \
    CHECK_TRUE(bw >= (float)(MIN_BW), "%s failed: expected minimal BW %d, got %f", DESC, MIN_BW, CVA6V_PRINTF_FLOAT(bw)); \
  })


int main() {
  printf("Starting bottleneck analysis ...\n");

  // warm up page tables
  {
    size_t     vl = __riscv_vsetvl_e8m8(sizeof(l1_buf));
    vuint8m8_t v8 = __riscv_vmv_v_x_u8m8(0, vl);
    __riscv_vse8_v_u8m8(l1_buf, v8, vl);
    __riscv_vse8_v_u8m8(ddr_buf, v8, vl);
    // wait until Raptor is idle by reading vl
    long unsigned tmp = 0;
    asm volatile("csrr %0, vl" : "=r"(tmp));
  }

  // Unit-strided access into L1 (all interfaces active, 16 bytes per transaction)
  // Expected BW utilization: 100% (128 bytes / cycle, pass threshold: 120)
  size_t vl  = __riscv_vsetvl_e8m8(sizeof(l1_buf));
  long   len = TEST_PAYLOAD_SZ;
  CHECK_BANDWIDTH(
    vuint8m8_t v8 = __riscv_vmv_v_x_u8m8(0x5A, vl),
    for (; len >= 0; len -= vl) { __riscv_vse8_v_u8m8(l1_buf, v8, vl); }, TEST_PAYLOAD_SZ, 120, 128,
    "L1 unit-strided :");

  // Special stride 4, carried out as a dense access (all interfaces active, 4 bytes per transaction)
  // Expected BW utilization: 25% (32 bytes / cycle, pass threshold: 30)
  vl  = __riscv_vsetvl_e8m8(sizeof(l1_buf) / 4);
  len = TEST_PAYLOAD_SZ;
  CHECK_BANDWIDTH(
    vuint8m8_t v8 = __riscv_vmv_v_x_u8m8(0x5B, vl),
    for (; len >= 0; len -= vl) { __riscv_vsse8_v_u8m8(l1_buf, 4, v8, vl); }, TEST_PAYLOAD_SZ, 30, 128,
    "L1 e8  stride 4 :");

  // Sparse access with intentional bank conflicts between adjacent memory ports (all interfaces, 2 bytes per transaction)
  // Expected BW utilization: 12.5% (16 bytes / cycle, pass threshold: 15)
  // Note: Using a load instead of a store here to avoid self-inflicted address collisions in L1 memory address filter.
  vl  = __riscv_vsetvl_e16m8(sizeof(l1_buf) / 16);
  len = TEST_PAYLOAD_SZ / sizeof(uint16_t);
  CHECK_BANDWIDTH(
    size_t bstride = 12,
    for (; len >= 0; len -= vl) {
      asm volatile("vlse16.v v8, (%0), %1" ::"r"(l1_buf), "r"(bstride) : "v8", "v9", "v10", "v11", "v12", "v13", "v14", "v15");
    },
    TEST_PAYLOAD_SZ, 15, 128, "L1 e16 stride 12:");

  // Sparse access without self-inflicted bank conflicts (4 interfaces active, 4 bytes per transaction
  // Expected BW utilization: 12.5% (16 bytes / cycle, pass threshold: 15)
  vl  = __riscv_vsetvl_e32m8(sizeof(l1_buf) / 16);
  len = TEST_PAYLOAD_SZ / sizeof(uint32_t);
  CHECK_BANDWIDTH(
    vuint32m8_t v32 = __riscv_vmv_v_x_u32m8(0x5A4B3C2D, vl),
    for (; len >= 0; len -= vl) { __riscv_vsse32_v_u32m8((uint32_t *)l1_buf, 16, v32, vl); }, TEST_PAYLOAD_SZ, 15,
    128, "L1 e32 stride 16:");

  // Unit-strided access into DDR (all interfaces active, 16 bytes per transaction)
  // No expectations w.r.t. bandwidth utilization (pass threshold: 0)
  vl  = __riscv_vsetvl_e8m8(sizeof(ddr_buf));
  len = TEST_PAYLOAD_SZ;
  CHECK_BANDWIDTH(
    vuint8m8_t v8 = __riscv_vmv_v_x_u8m8(0x5C, vl),
    for (; len >= 0; len -= vl) { __riscv_vse8_v_u8m8(ddr_buf, v8, vl); }, TEST_PAYLOAD_SZ, 0, 128,
    "DDR unit-strided:");

  return testcase_finalize();
}
