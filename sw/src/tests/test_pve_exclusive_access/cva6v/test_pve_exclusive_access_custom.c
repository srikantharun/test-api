#include <printf.h>
#include <testutils.h>
#include <barrier.h>
#include <hw_defines.h>

#define NUM_ITERATIONS 4    // Number of times to reuse the barrier

// Shared variables
atomic_int __attribute__((section(".sys_spm"))) before_barrier_count;
atomic_int __attribute__((section(".sys_spm"))) after_barrier_count;

// Barrier structure
barrier_t __attribute__((section(".sys_spm"))) test_barrier;

// Thread function
int barrier_thread_function(void* arg) {
  UNUSED(arg);

  for (int iter = 0; iter < NUM_ITERATIONS; iter++) {
      // Increment before_barrier_count to signal reaching the barrier
      atomic_fetch_add(&before_barrier_count, 1);

      // Wait at the barrier
      barrier_wait(&test_barrier);

      // Increment after_barrier_count to signal exiting the barrier
      atomic_fetch_add(&after_barrier_count, 1);
  }
  return 0;
}


int main() {
  testcase_init();

  uint64_t core_id = r_mhartid();

  if (core_id == PVE_0_CLUSTER_0_CORE_0){
      // Initialize shared counters
      atomic_init(&before_barrier_count, 0);
      atomic_init(&after_barrier_count, 0);

      // Initialize the barrier with the number of cores
      barrier_init(&test_barrier, HW_DEFINES_PVE_0_CORE_NUMBER );
  }

  CHECK_EQUAL_INT(TEST_SUCCESS, barrier_thread_function(NULL));

  int expected_count = HW_DEFINES_PVE_0_CORE_NUMBER  * NUM_ITERATIONS;
  int actual_before = atomic_load(&before_barrier_count);
  int actual_after = atomic_load(&after_barrier_count);

  // Check if all threads reached the barrier
  CHECK_TRUE(actual_before == expected_count, "Not all threads reached the barrier.");
  CHECK_TRUE(actual_after == expected_count, "Not all threads passed the barrier.");
  CHECK_TRUE(test_barrier.generation == NUM_ITERATIONS, "Generation does not match the expected number of iterations.");

  return testcase_finalize();
}

