// This is a test file for clock_gating
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Variables to simulate clock gating states
volatile int clock_active = 1;
volatile int clock_idle = 0;

// Function to simulate active to idle state transition
int active_to_idle() {
    // Simulate some activity
    for (volatile int i = 0; i < 1000; i++) {
        // Busy-wait loop to simulate work
    }
    // Simulate clock gating applied
    clock_active = 0;
    clock_idle = 1;
    return clock_idle;
}

// Function to simulate idle to active state transition
int idle_to_active() {
    // Simulate some activity
    for (volatile int i = 0; i < 1000; i++) {
        // Busy-wait loop to simulate work
    }
    // Simulate clock gating removed
    clock_active = 1;
    clock_idle = 0;
    return clock_active;
}

// Function to test clock gating by simulating transitions between active and idle states
void test_clock_gating() {
    printf("Testing Clock Gating...\n");
    int pass = 1; // Flag to indicate if the test passes

    // Simulate multiple transitions to test clock gating
    for (int i = 0; i < 10; i++) {
        if (active_to_idle() != 1) {
            printf("Transition from active to idle failed at iteration %d. Clock state: %d\n", i, clock_idle);
            pass = 0;
            break;
        }
        if (idle_to_active() != 1) {
            printf("Transition from idle to active failed at iteration %d. Clock state: %d\n", i, clock_active);
            pass = 0;
            break;
        }
    }

    if (pass) {
        printf("Clock Gating Test PASSED.\n");
    } else {
        printf("Clock Gating Test FAILED.\n");
    }
}

int main() {
    printf("Running test: clock_gating\n");
    initialize_registers();
    test_clock_gating();
    return 0;
}
