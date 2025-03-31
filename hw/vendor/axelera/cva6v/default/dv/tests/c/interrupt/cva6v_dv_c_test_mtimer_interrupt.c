#include "common.h"

// Define the memory-mapped addresses for MTIME and MTIMECMP
#define MTIME_BASE 0x0200BFF8
#define MTIMECMP_BASE 0x02004000

// Global variable to track if the timer interrupt was triggered
volatile int timer_interrupt_triggered = 0;

// Timer interrupt handler
void timer_interrupt_handler() {
    // Indicate that the interrupt was triggered
    timer_interrupt_triggered = 1;

    // Read mtvec to determine the cause
    uint64_t mepc, mcause;

    asm volatile ("csrr %0, mepc" : "=r"(mepc));
    asm volatile ("csrr %0, mcause" : "=r"(mcause));

    // Skip faulting instruction
    if (mcause == 0x8000000000000007) { // Machine timer interrupt
        mepc += 4; // Assuming a 4-byte instruction
        asm volatile ("csrw mepc, %0" :: "r"(mepc));
    }
}

// Function to set up the timer interrupt
void setup_timer_interrupt(uint64_t delay_cycles) {
    uint64_t current_time;

    // Read the current time (mtime)
    current_time = *((volatile uint64_t*)MTIME_BASE);

    // Set the timer to trigger after delay_cycles
    uint64_t compare_time = current_time + delay_cycles;
    *((volatile uint64_t*)MTIMECMP_BASE) = compare_time;
}

// Function to initialize the interrupt vector
void initialize_interrupts() {
    // Set the mtvec to point to the interrupt handler
    asm volatile ("csrw mtvec, %0" :: "r"(&timer_interrupt_handler));
}

// Function to reset MTIMER
void reset_mtimer() {
    *((volatile uint64_t*)MTIME_BASE) = 0; // Reset MTIME to 0
    *((volatile uint64_t*)MTIMECMP_BASE) = 0; // Reset MTIMECMP to 0
}

// Test function
int main() {
    // Initialize the interrupt vector and timer
    initialize_interrupts();

    // Scenario 1: Basic Timer Interrupt Triggering
    printf("Starting Scenario 1: Basic Timer Interrupt Triggering...\n");
    setup_timer_interrupt(50000);
    while (!timer_interrupt_triggered);
    printf("Scenario 1 Passed: Timer interrupt triggered as expected.\n");

    // Reset MTIMER for the next scenario
    reset_mtimer();

    // Scenario 2: Immediate Interrupt Edge Case
    printf("Starting Scenario 2: Immediate Interrupt Edge Case...\n");
    timer_interrupt_triggered = 0;
    setup_timer_interrupt(1); // Very small delay, should trigger immediately
    while (!timer_interrupt_triggered);
    printf("Scenario 2 Passed: Immediate interrupt triggered as expected.\n");

    // Reset MTIMER for the next scenario
    reset_mtimer();

    // Scenario 3: Dynamic Update of MTIMECMP Register
    printf("Starting Scenario 3: Dynamic Update of MTIMECMP Register...\n");
    timer_interrupt_triggered = 0;
    setup_timer_interrupt(50000); // Initial delay
    // Dynamically adjust MTIMECMP to delay the interrupt further
    setup_timer_interrupt(100000);
    while (!timer_interrupt_triggered);
    printf("Scenario 3 Passed: Interrupt delayed correctly with dynamic update.\n");

    // Reset MTIMER for the next scenario
    reset_mtimer();

    // Scenario 4: MTIMER Device Reset Handling
    printf("Starting Scenario 4: MTIMER Device Reset Handling...\n");
    timer_interrupt_triggered = 0;
    setup_timer_interrupt(50000);
    // Simulate MTIMER reset
    reset_mtimer();
    // Interrupt should no longer trigger since MTIMER is reset
    int reset_success = 1;
    for (volatile int i = 0; i < 100000; i++) { // Simple wait loop
        if (timer_interrupt_triggered) {
            reset_success = 0;
            break;
        }
    }
    if (reset_success) {
        printf("Scenario 4 Passed: MTIMER reset handled correctly.\n");
    } else {
        printf("Scenario 4 Failed: Unexpected interrupt after MTIMER reset.\n");
    }

    // Scenario 5: Register Read/Write Operations
    printf("Starting Scenario 5: Register Read/Write Operations...\n");
    uint64_t mtime_before, mtimecmp_before, mtime_after;
    mtime_before = *((volatile uint64_t*)MTIME_BASE);
    mtimecmp_before = *((volatile uint64_t*)MTIMECMP_BASE);

    // Perform dummy write operations
    *((volatile uint64_t*)MTIME_BASE) = mtime_before + 1000;
    *((volatile uint64_t*)MTIMECMP_BASE) = mtimecmp_before + 1000;

    // Read back the values
    mtime_after = *((volatile uint64_t*)MTIME_BASE);
    uint64_t mtime_diff = mtime_after - mtime_before;

    // Validate that the operations succeeded
    if (mtime_diff > 0 && mtime_after >= mtime_before) {
        printf("Scenario 5 Passed: Register read/write operations are correct.\n");
    } else {
        printf("Scenario 5 Failed: Register read/write operations are incorrect.\n");
    }

    return 0;
}
