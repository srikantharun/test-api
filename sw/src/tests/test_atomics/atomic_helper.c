#include <testutils.h>
#include <atomics.h>
#include <asm.h>

// global variables used for atomic tests
atomic_uint64_t __attribute__((section(".sys_spm"))) result_add;
atomic_uint64_t __attribute__((section(".sys_spm"))) test_add;

atomic_uint64_t __attribute__((section(".sys_spm"))) result_cas;

atomic_uint64_t __attribute__((section(".sys_spm"))) result_or;
atomic_uint64_t __attribute__((section(".sys_spm"))) test_or;

atomic_uint64_t __attribute__((section(".sys_spm"))) result_swap;
atomic_uint64_t __attribute__((section(".sys_spm"))) test_swap;

void test_atomics_basic() {
  // test atomic add
  result_add = 3;
  test_add = 0;
  test_add = atomic_add(&result_add, 2);

  CHECK_EQUAL_INT(5, result_add);
  CHECK_EQUAL_INT(3, test_add);

  // test atomic cas
  uint64_t expected = 3;
  uint64_t desired = 5;
  result_cas = 3;
  CHECK_TRUE(atomic_cas(&result_cas, &expected, desired));
  CHECK_EQUAL_INT(5, result_cas);

  // test atomic or
  result_or = 0b00110011;
  test_or = 0;
  test_or = atomic_or(&result_or, 0b11001100);
  CHECK_EQUAL_INT(0b11111111, result_or);
  CHECK_EQUAL_INT(0b00110011, test_or);

  // test atomic swap
  result_swap = 0;
  test_swap = atomic_swap(&result_swap, 7);
  CHECK_EQUAL_INT(7, result_swap);
  CHECK_EQUAL_INT(0, test_swap);

  test_swap = atomic_swap(&result_swap, 3);
  CHECK_EQUAL_INT(3, result_swap);
  CHECK_EQUAL_INT(7, test_swap);
}

// Global variable to test atomic lock
atomic_flag __attribute__((section(".sys_spm"))) lock_test = ATOMIC_FLAG_INIT;

// Test atomic lock operations
void test_atomic_lock() {
  // Acquire the lock using atomic test_and_set
  atomic_lock_acquire(&lock_test);

  // Check if the lock is acquired successfully
  CHECK_TRUE(atomic_flag_test_and_set(&lock_test) == 1);

  // Release the lock using atomic release
  atomic_lock_release(&lock_test);

  // Check if the lock is released successfully
  CHECK_TRUE(atomic_flag_test_and_set(&lock_test) == 0);

  // Release the lock again using atomic release
  atomic_flag_clear(&lock_test);
}

int test_atomic_helper(void *arg) {
  UNUSED(arg);
  printf("*** Atomic tests starts on core %d!\n", r_mhartid());

  test_atomics_basic();
  test_atomic_lock();

  return TEST_SUCCESS;
}
