#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>

extern uint64_t __attribute__((aligned(64), section(".ddr"))) ddr_data[];
extern uint64_t __attribute__((aligned(64))) expected_data[];

int main() {
  printf("APU started\n");

  testcase_init();

  // Compare each value of ddr_data with expected_data
  for (uint32_t i = 0; i < 128; i++) {
    CHECK_EQUAL_INT(expected_data[i], ddr_data[i], "DDR data check failed at index %d.", i);
  }

  /* END TEST */
  return testcase_finalize();
}
