// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
// Author: Abhilash Chadhar

#include "common.h"  // Include the common header file with printf support

#include <math.h>
#include <printf.h>
#include <stdbool.h>


// Function prototypes
int main();
void m_mode();
void s_mode();
void u_mode();

// Exception handler for Supervisor mode
void s_exception_handler();

// Global variables for testing
volatile int test_variable = 0;
volatile int test_iterations = 0;      // Counter for the number of test iterations
volatile int m_mode_reached = 0;       // Flag to indicate M-mode was reached
#define MAX_TEST_ITERATIONS 1          // Set the desired number of test iterations

// Entry point
int main() {
    testcase_init();  // Initialize test case counters

    printf("Starting in Machine mode (M-mode)\n");

    // Delegate both Instruction Access Fault (scause=1) and Illegal Instruction (scause=2) to S-mode
    asm volatile(
        "li t0, 0x6\n"    // 0x6 = (1 << 1) | (1 << 2)
        "csrw medeleg, t0\n"
    );

    // Verify and print medeleg
    uintptr_t medeleg_val;
    asm volatile(
        "csrr %0, medeleg\n"
        : "=r"(medeleg_val)
        :
        : "memory"
    );
    printf("medeleg set to 0x%lx\n", medeleg_val);
    printf("Delegated Instruction Access Fault and Illegal Instruction exceptions to S-mode\n");

    // Set the Machine mode exception handler
    asm volatile(
        "la t0, m_mode\n"       // Load address of m_mode
        "csrw mtvec, t0\n"      // Set mtvec to m_mode
    );
    printf("Set M-mode exception handler\n");

    printf("Switching to Supervisor mode (S-mode)\n");

    // Switch to Supervisor mode
    asm volatile(
        // Set MSTATUS.MPP to Supervisor mode
        "csrr t0, mstatus\n"
        "li t1, %0\n"            // t1 = MSTATUS_MPP_S (0x0800)
        "li t2, %1\n"            // t2 = MSTATUS_MPP_MASK (0x1800)
        "not t2, t2\n"           // t2 = ~MSTATUS_MPP_MASK
        "and t0, t0, t2\n"       // Clear MPP bits
        "or t0, t0, t1\n"        // Set MPP to S-mode
        "csrw mstatus, t0\n"     // Update mstatus
        // Set MEPC to s_mode function
        "la t0, s_mode\n"
        "csrw mepc, t0\n"
        // MRET to switch to S-mode
        "mret\n"
        :
        : "i"(MSTATUS_MPP_S), "i"(MSTATUS_MPP_MASK)
        : "t0", "t1", "t2"
    );

    // Should not reach here
    printf("Error: Returned to main after mret to S-mode\n");
    return TEST_FAILURE;  // Use TEST_FAILURE instead of looping

    // Note: The following return is redundant but added for completeness
    // return testcase_finalize();  // Finalize the test case
}

void m_mode() {
    printf("Entered Machine mode exception handler (m_mode)\n");

    // Read mcause to determine the cause of the exception
    uintptr_t mcause, mepc, mtval;
    asm volatile(
        "csrr %0, mcause\n"
        "csrr %1, mepc\n"
        "csrr %2, mtval\n"
        : "=r"(mcause), "=r"(mepc), "=r"(mtval)
        :
        : "memory"
    );

    printf("M-mode exception: mcause=0x%lx, mepc=0x%lx, mtval=0x%lx\n", mcause, mepc, mtval);

    // Check if the cause is environment call from S-mode (mcause == 9)
    if ((mcause & 0xFF) == 9) {
        printf("Handled environment call from S-mode in M-mode\n");
        printf("Test completed successfully in M-mode exception handler.\n");
        exit(TEST_SUCCESS);  // Report success and exit
    } else {
        printf("Unhandled exception in M-mode. mcause: 0x%lx\n", mcause);
        exit(TEST_FAILURE);  // Report failure
    }
}

void s_mode() {
    printf("Entered Supervisor mode (S-mode)\n");

    // Set the Supervisor mode exception handler
    asm volatile(
        "la t0, s_exception_handler\n"
        "csrw stvec, t0\n"
    );

    // Check if the test is complete
    if (test_iterations >= MAX_TEST_ITERATIONS) {
        printf("Test iterations completed in S-mode.\n");
        // Transition back to M-mode via ecall
        printf("Transitioning back to M-mode via ecall.\n");
        asm volatile("ecall");
        exit(TEST_SUCCESS);  // Report success and exit
    }

    printf("Switching to User mode (U-mode)\n");

    // Switch to User mode
    asm volatile(
        // Set SSTATUS.SPP to User mode
        "csrr t0, sstatus\n"
        "li t1, %0\n"            // t1 = SSTATUS_SPP_MASK (0x0100)
        "not t1, t1\n"           // t1 = ~SSTATUS_SPP_MASK
        "and t0, t0, t1\n"       // Clear SPP bit (set to U-mode)
        "csrw sstatus, t0\n"
        // Set SEPC to u_mode function
        "la t0, u_mode\n"
        "csrw sepc, t0\n"
        // SRET to switch to U-mode
        "sret\n"
        :
        : "i"(SSTATUS_SPP_MASK)
        : "t0", "t1"
    );

    // Should not reach here
    printf("Error: Returned to s_mode after sret to U-mode\n");
    exit(TEST_FAILURE);  // Report failure
}

void u_mode() {
    printf("Entered User mode (U-mode)\n");

    // Perform operations to test structural hazards
    for (volatile int i = 0; i < 10; i++) {
        test_variable += i;
        test_variable *= 2;
        test_variable /= 3;
        test_variable -= i;
        // Load and store operations
        volatile int temp = test_variable;
        test_variable = temp + i;
        printf("Iteration %d: test_variable = %d\n", i, test_variable);
    }

    printf("User mode operations completed\n");
    printf("Causing an illegal instruction to trigger exception handler\n");

    // Cause an illegal instruction exception to switch back to Supervisor mode
    asm volatile(".word 0xFFFFFFFF\n");

    // Should not reach here
    printf("Error: Returned to u_mode after illegal instruction\n");
    exit(TEST_FAILURE);  // Report failure
}

// Supervisor mode exception handler
void s_exception_handler() {
    printf("Entered Supervisor mode exception handler\n");

    uintptr_t scause, sepc, stval;
    asm volatile(
        "csrr %0, scause\n"
        "csrr %1, sepc\n"
        "csrr %2, stval\n"
        : "=r"(scause), "=r"(sepc), "=r"(stval)
        :
        : "memory"
    );
    printf("S-mode exception: scause=0x%lx, sepc=0x%lx, stval=0x%lx\n", scause, sepc, stval);

    // Extract the exception code (lower bits)
    uintptr_t ecause = scause & 0xFF;

    // Check if the exception is Instruction Access Fault (1) or Illegal Instruction (2)
    if (ecause == 1 || ecause == 2) {
        printf("Handled exception %ld in S-mode\n", ecause);
        test_iterations++;

        // Check if test iterations are complete
        if (test_iterations >= MAX_TEST_ITERATIONS) {
            printf("Test iterations completed in exception handler. Transitioning to M-mode via ecall.\n");
            // Cause an environment call from S-mode to transition to M-mode
            asm volatile("ecall");
            exit(TEST_SUCCESS);  // Report success and exit
        } else {
            // Resume execution in S-mode by setting SEPC to s_mode
            asm volatile(
                "la t0, s_mode\n"
                "csrw sepc, t0\n"
                "sret\n"
            );
        }
    } else {
        printf("Unhandled exception in S-mode. scause: 0x%lx\n", scause);
        exit(TEST_FAILURE);  // Report failure
    }
}
