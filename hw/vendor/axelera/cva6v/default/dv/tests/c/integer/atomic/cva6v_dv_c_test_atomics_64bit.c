// test_atomics_toggle.c
#include <stdint.h>
#include "common.h"
// Declare the assembly test function
extern void run_atomics_64b_tests();

int main() {
    // Initialize the test case
    // Call the assembly test function

    testcase_init(); // Initialize test case counters
    run_atomics_64b_tests();

    CHECK_TRUE(1);

    if (testcase_finalize() == TEST_SUCCESS) {
        printf("All tests passed.\n");
    } else {
        printf("Some tests failed.\n");
    }

    return 0;
}
