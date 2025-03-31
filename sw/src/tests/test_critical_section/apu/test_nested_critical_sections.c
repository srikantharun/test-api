#include <testutils.h>
#include <critical_section.h>
#include <timer.h>

atomic_flag lock_sectionA = ATOMIC_FLAG_INIT;
atomic_flag lock_sectionB = ATOMIC_FLAG_INIT;

uint64_t shared_variable = 0;

void sectionB() {
  enter_critical_section(&lock_sectionB);
  // Perform some operations within the critical section
  shared_variable += 2;
  exit_critical_section(&lock_sectionB);
}

void sectionA() {
  enter_critical_section(&lock_sectionA);
  // Perform some operations within the critical section
  shared_variable++;
  sectionB();
  exit_critical_section(&lock_sectionA);
}

void test_standard_nested_sections()
{
  shared_variable = 0;
  sectionA();
  CHECK_EQUAL_INT(3, shared_variable);
}

void test_sectionB_precedes_sectionA()
{
  shared_variable = 0;
  sectionB();
  sectionA();
  CHECK_EQUAL_INT(5, shared_variable);
}

void test_high_load_stress()
{
  shared_variable = 0;
  const int stressTestIterations = 10000;
  for (int i = 0; i < stressTestIterations; ++i) {
    sectionA();
  }
  CHECK_EQUAL_INT(3 * stressTestIterations, shared_variable);
}


int main() {
  testcase_init();

  /* START TEST */
  printf("*** Nested Critical Sections Test starts!\n");

  test_standard_nested_sections();
  test_sectionB_precedes_sectionA();
  test_high_load_stress();

  /* END TEST */
  return testcase_finalize();
}

