#pragma once

#include <platform.h>
#include <barrier.h>
#include <stdatomic.h>

#define EXCLUSIVE_APU_CORE_NUM  (HW_DEFINES_APU_CORE_NUMBER - 1)
#define EXCLUSIVE_PVE0_CORE_NUM HW_DEFINES_PVE_0_CORE_NUMBER
#define EXCLUSIVE_PVE1_CORE_NUM HW_DEFINES_PVE_1_CORE_NUMBER
#define EXCLUSIVE_AICORE_NUM    HW_DEFINES_AICORE_MODULE_NUMBER
#define EXCLUSIVE_CORE_NUM      (EXCLUSIVE_APU_CORE_NUM + EXCLUSIVE_PVE0_CORE_NUM + EXCLUSIVE_PVE1_CORE_NUM + EXCLUSIVE_AICORE_NUM)

#define NUM_ITERATIONS 4 // Number of times to reuse the barrier


// Avoid unaligned AXI transactions, use 64bit aligned variables
typedef struct {
    barrier_t test_barrier;
    atomic_long before_barrier_count; // Number of threads that have reached the barrier
    atomic_long after_barrier_count;  // Barrier generation to allow reuse
    volatile long before_barrier_counts[NUM_CORES];
    volatile long after_barrier_counts[NUM_CORES];
    volatile long assert;
} exclusive_access_t;

int is_core_active(uint64_t i);
int barrier_thread_function(void* arg);
