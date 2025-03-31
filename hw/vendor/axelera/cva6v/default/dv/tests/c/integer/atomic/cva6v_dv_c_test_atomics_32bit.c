// test_atomics_toggle.c
#include <stdint.h>
#include "common.h"
// Declare the assembly test function
extern void run_atomics_32b_tests();

int main() {
    // Initialize the test case
    // Call the assembly test function
    run_atomics_32b_tests();

    return 0;
}
