#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <printf.h>


int main() {

  testcase_init();

  // Start all cores
  start_cores_available();

  // Wait for all cores
  for(uint32_t i = AI_CORE_0; i < AI_CORE_0 + NUM_CORES; i++) {
    if (is_core_available(i))
        CHECK_EQUAL_INT(i, wait_core(i));
  }

  return testcase_finalize();
}
