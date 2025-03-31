#pragma once

#include <stdint.h>
#include <atomics.h>
#include <asm.h>

typedef struct {
    atomic_flag lock;
    uint64_t owner;
    int recursion_count;
} reentrant_lock_t;

#define REENTRANT_LOCK_INIT { ATOMIC_FLAG_INIT, UINT64_MAX, 0 }

/**
 * @brief Acquires a reentrant lock.
 *
 * This function acquires a reentrant lock. If the current thread already owns the lock,
 * it increments the recursion count and returns immediately. Otherwise, it spins until
 * the lock becomes available, then acquires it and sets the current thread as the owner.
 *
 * @param lock Pointer to the reentrant lock to be acquired.
 */
void reentrant_lock_acquire(reentrant_lock_t *lock);

/**
 * @brief Releases a reentrant lock.
 *
 * This function releases a reentrant lock. If the current thread owns the lock,
 * it decrements the recursion count. If the recursion count reaches zero, it clears
 * the lock and sets the owner to an invalid thread ID. If the current thread does
 * not own the lock, the function returns without making any changes.
 *
 * @param lock Pointer to the reentrant lock to be released.
 */
void reentrant_lock_release(reentrant_lock_t *lock);
