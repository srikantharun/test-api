#include <testutils.h>
#include <atomics.h>

uint32_t volatile test_var = 0;

static void test_lrsc_without_reservation() {
  test_var = 0;
  asm volatile("la a0, test_var\n\t"
               "li a5, 0xdeadbeef\n\t"
               "sc.w a4, a5, (a0)\n\t"
               : : : "a0", "a4", "a5", "memory");
  CHECK_TRUE(test_var == 0);
}

static void test_lrsc_with_reservation() {
  test_var = 0;
  asm volatile("la a0, test_var\n\t"
               "lr.w a4, (a0)\n\t"
               "li a5, 0xdeadbeef\n\t"
               "sc.w a4, a5, (a0)\n\t"
               : : : "a0", "a4", "a5", "memory");
  CHECK_EQUAL_INT(0xdeadbeef, test_var);
}

int main() {
  testcase_init();
  /* START TEST */
  printf("*** Atomic LR/SC tests starts!\n");
  test_lrsc_without_reservation();
  test_lrsc_with_reservation();
  /* END TEST */
  return testcase_finalize();
}

