#pragma once

#include <stdatomic.h>

// Barrier structure
typedef struct {
    atomic_long count;       // Number of threads that have reached the barrier
    atomic_long generation;  // Barrier generation to allow reuse
    int total;              // Total number of threads to wait for
} barrier_t;


// Initialize the barrier
void barrier_init(barrier_t *barrier, int total);
// Wait at the barrier. Can be use for synchronizing the threads.
void barrier_wait(barrier_t *barrier);
