// test_atomics_toggle.c
#include <stdint.h>
#include "common.h"
// Declare the assembly test function
extern void run_atomic_tests();

int main() {
    // Initialize the test case
    // Call the assembly test function
    run_atomic_tests();

    return 0;
}
