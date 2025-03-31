#include <thread.h>
#include <printf.h>
#include <testutils.h>
#include <barrier.h>
#include <hw_defines.h>

#define NUM_ITERATIONS 4    // Number of times to reuse the barrier

// Shared variables
atomic_int before_barrier_count;
atomic_int after_barrier_count;

// Barrier structure
barrier_t test_barrier;

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

  // Initialize shared counters
  atomic_init(&before_barrier_count, 0);
  atomic_init(&after_barrier_count, 0);

  // Initialize the barrier with the number of cores
  barrier_init(&test_barrier, HW_DEFINES_APU_CORE_NUMBER );

  // Create threads
  for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER ; i++) {
      thread_launch(i, barrier_thread_function, NULL);
  }

  barrier_thread_function(NULL);

  thread_join_all();

  int expected_count = HW_DEFINES_APU_CORE_NUMBER  * NUM_ITERATIONS;
  int actual_before = atomic_load(&before_barrier_count);
  int actual_after = atomic_load(&after_barrier_count);

  printf("Barrier Test Results:\n");
  printf("Expected before_barrier_count: %d\n", expected_count);
  printf("Actual before_barrier_count:   %d\n", actual_before);
  printf("Expected after_barrier_count:  %d\n", expected_count);
  printf("Actual after_barrier_count:    %d\n", actual_after);

  printf("Generation %d\n", test_barrier.generation);
  printf("Count %d\n", test_barrier.count);
  printf("Total %d\n", test_barrier.total);

  // Check if all threads reached the barrier
  CHECK_TRUE(actual_before == expected_count, "Not all threads reached the barrier.");
  CHECK_TRUE(actual_after == expected_count, "Not all threads passed the barrier.");
  CHECK_TRUE(test_barrier.generation == NUM_ITERATIONS, "Generation does not match the expected number of iterations.");

  return testcase_finalize();
}

