#include <reentrant_lock.h>

void reentrant_lock_acquire(reentrant_lock_t *lock) {
    uint64_t current_thread = r_uhartid();

    // if thread has already acquired the lock then increment
    if (lock->owner == current_thread) {
        lock->recursion_count++;
        return;
    }

    // spin until lock is free
    atomic_lock_acquire(&(lock->lock));

    lock->owner = current_thread;
    lock->recursion_count++;
}

void reentrant_lock_release(reentrant_lock_t *lock) {
    if (lock->owner != r_uhartid()) {
        // Error: Unlocking a lock not owned by the current thread
        return;
    }

    if (--(lock->recursion_count) == 0) {
        lock->owner = UINT64_MAX;
        atomic_lock_release(&(lock->lock));
    }
}
