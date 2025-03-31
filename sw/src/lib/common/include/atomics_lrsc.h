#include <platform.h>
#include <atomics.h>

void atomic_init_lrsc(volatile atomic_long* ptr, const long val);
long atomic_fetch_add_lrsc(volatile atomic_long* ptr, long val);
void atomic_store_lrsc(volatile atomic_long* ptr, long val);
long atomic_load_lrsc(volatile atomic_long* ptr);
