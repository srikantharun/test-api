#pragma once

#include <stdint.h>
#include <stdatomic.h>

typedef _Atomic uint64_t atomic_uint64_t;

// Atomic operation macros using stdatomic.h

/*
 * Performs an atomic fetch-and-add operation.
 * Inputs:
 *   - ptr: Pointer to the atomic variable.
 *   - inc: Value to add to the atomic variable.
 * Returns:
 *   - The original value of the atomic variable before the addition.
 */
#define atomic_add(ptr, inc)             atomic_fetch_add(ptr, inc)

/*
 * Performs an atomic fetch-and-or operation.
 * Inputs:
 *   - ptr: Pointer to the atomic variable.
 *   - inc: Value to OR with the atomic variable.
 * Returns:
 *   - The original value of the atomic variable before the OR operation.
 */
#define atomic_or(ptr, inc)              atomic_fetch_or(ptr, inc)

/*
 * Performs an atomic exchange operation.
 * Inputs:
 *   - ptr: Pointer to the atomic variable.
 *   - swp: Value to exchange with the atomic variable.
 * Returns:
 *   - The original value of the atomic variable before the exchange.
 */
#define atomic_swap(ptr, swp)            atomic_exchange(ptr, swp)

/*
 * Performs an atomic compare-and-swap operation.
 * Inputs:
 *   - ptr: Pointer to the atomic variable.
 *   - cmp: Pointer to the expected value.
 *   - swp: Value to set if the current value of the atomic variable matches the expected value.
 * Returns:
 *   - true if the swap was successful (the value in ptr was equal to the expected value).
 *   - false if the swap was not successful (the value in ptr was not equal to the expected value, and the expected value is updated to the actual value).
 */
#define atomic_cas(ptr, cmp, swp)        atomic_compare_exchange_strong(ptr, cmp, swp)


static inline void atomic_lock_acquire(atomic_flag *lock) {
    while (atomic_flag_test_and_set(lock)) {
        // Spin until the lock is acquired
    }
}

static inline void atomic_lock_release(atomic_flag *lock) {
    // Release the lock
    atomic_flag_clear(lock);
}
