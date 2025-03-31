// Sanity check for the test framework (testutils.{h,c}).
// This test does not check anything useful.

#include <stdbool.h>
#include <testutils.h>

int main() {
  testcase_init();

  int error = 0;

  // Check correct return value for eac CHECK_*
  error += !(true == CHECK_TRUE(1, "This test is designed to pass!"));
  error += !(false == CHECK_TRUE(0, "This test is designed to fail!"));
  error += !(true == CHECK_EQUAL_INT(1, 1, "This test is designed to pass!"));
  error += !(false == CHECK_EQUAL_INT(1, 2, "This test is designed to fail!"));
  error += !(true == CHECK_EQUAL_FLOAT(3.1415926, 3.1415926, "This test is designed to pass!"));
  error += !(false == CHECK_EQUAL_FLOAT(3.1415926, 42.0001, "This test is designed to fail!"));
  error += !(true == CHECK_EQUAL_CHAR('A', 'A', "This test is designed to pass!"));
  error += !(false == CHECK_EQUAL_CHAR('A', 'B', "This test is designed to fail!"));

  error += !(testcase_finalize() == TEST_FAILURE);

  // Check correct fail/pass counting
  testcase_init();
  CHECK_TRUE(1, "This test is designed to pass!");
  error += !(testcase_finalize() == TEST_SUCCESS);

  testcase_init();
  CHECK_TRUE(0, "This test is designed to fail!");
  error += !(testcase_finalize() == TEST_FAILURE);

  testcase_init();
  CHECK_EQUAL_INT(1, 1, "This test is designed to pass!");
  error += !(testcase_finalize() == TEST_SUCCESS);

  testcase_init();
  CHECK_EQUAL_INT(1, 2, "This test is designed to fail!");
  error += !(testcase_finalize() == TEST_FAILURE);

  testcase_init();
  CHECK_EQUAL_FLOAT(3.1415926, 3.1415926, "This test is designed to pass!");
  error += !(testcase_finalize() == TEST_SUCCESS);

  testcase_init();
  CHECK_EQUAL_FLOAT(3.1415926, 42.0001, "This test is designed to fail!");
  error += !(testcase_finalize() == TEST_FAILURE);

  testcase_init();
  CHECK_EQUAL_CHAR('A', 'A', "This test is designed to pass!");
  error += !(testcase_finalize() == TEST_SUCCESS);

  testcase_init();
  CHECK_EQUAL_CHAR('A', 'B', "This test is designed to fail!");
  error += !(testcase_finalize() == TEST_FAILURE);


  /* COMMENT or UNCOMMENT manually for testing ASSERT */
  // ASSERT(0, "Test designed to fail! PROGRAM STOPS!");
  // ASSERT(1<5 && 5<4, "Test designed to fail! PROGRAM STOPS!");

  if (error == 0){
    return TEST_SUCCESS;
  }

  return TEST_FAILURE;
}
