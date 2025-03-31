#include <atomics_lrsc.h>

/* Relaying on double word LR/SC for syncing 
 * https://git.axelera.ai/prod/europa/-/merge_requests/2745#note_303502 
 *
 * TODO: Interrupts should be disabled between LR and SC instruction calls.
 */


void atomic_init_lrsc(volatile atomic_long* ptr, const long val) {
    __asm__ __volatile__ (
        "mv t0, %1\n\t"            // Move 'val' into t0
        "atomic_init:\n\t"
        "lr.d t1, (%0)\n\t"        // Load-Reserved: Read current value (not needed for init)
        "sc.d t2, t0, (%0)\n\t"    // Store-Conditional: Attempt to store 'val'
        "bnez t2, atomic_init\n\t" // If SC fails (another core modified), retry
        :
        : "r" (ptr), "r" (val)
        : "t0", "t1", "t2", "memory"
    );
}

long atomic_fetch_add_lrsc(volatile atomic_long* ptr, long val) {
    long old;
    
    __asm__ __volatile__ (
        "atomic_add:\n\t"
        "lr.d t0, (%1)\n\t"    // Load-Reserved: Read the current value
        "add t1, t0, %2\n\t"   // Compute new value (old + val)
        "sc.d t2, t1, (%1)\n\t"// Store-Conditional: Attempt to write new value
        "bnez t2, atomic_add\n\t" // Retry if SC failed
        "mv %0, t0\n\t"        // Store original value in 'old'
        : "=&r" (old)          // Output: old value before addition
        : "r" (ptr), "r" (val) // Inputs: ptr (address), val (value to add)
        : "t0", "t1", "t2", "memory"
    );

    return old;  // Return the old value before addition
}

void atomic_store_lrsc(volatile atomic_long* ptr, long val) {
    __asm__ __volatile__ (
        "atomic_store:\n\t"
        "lr.d t0, (%0)\n\t"    // Load-Reserved (not actually needed, but required for SC)
        "sc.d t1, %1, (%0)\n\t"// Store-Conditional: Attempt to store 'val'
        "bnez t1, atomic_store\n\t" // Retry if SC failed
        :
        : "r" (ptr), "r" (val) // Inputs: ptr (address), val (value to store)
        : "t0", "t1", "memory"
    );
}

long atomic_load_lrsc(volatile atomic_long* ptr) {
    long val;

    __asm__ __volatile__ (
        "lr.d %0, (%1)\n\t"  // Load-Reserved: Read the current value atomically
        : "=r" (val)         // Output: val (loaded value)
        : "r" (ptr)          // Input: ptr (address to load from)
        : "memory"
    );

    return val;  // Return the loaded value
}
