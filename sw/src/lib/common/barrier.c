#include <barrier.h>
#include <atomics_lrsc.h>

/* Fences are used to make sure there is only one ongoing AXI excusive transaction per core */

// Initialize a barrier
void barrier_init(barrier_t *barrier, int total) {
  atomic_init_lrsc(&barrier->count, 0);
  atomic_init_lrsc(&barrier->generation, 0);
  barrier->total = total;
}

// Wait at the barrier
void barrier_wait(barrier_t *barrier) {
  int generation = atomic_load_lrsc(&barrier->generation);
  int count = atomic_fetch_add_lrsc(&barrier->count, 1) + 1;
  if (count == barrier->total) {
      // Last thread to arrive resets count and advances generation
      atomic_store_lrsc(&barrier->count, 0);
      atomic_fetch_add_lrsc(&barrier->generation, 1);
  } else {
      // Wait until the generation changes, indicating barrier completion
      while (atomic_load_lrsc(&barrier->generation) == generation){
        // Busy-wait
      };

  }
}
