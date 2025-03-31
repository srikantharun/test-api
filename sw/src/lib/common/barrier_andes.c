// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary
#include <barrier_andes.h>


extern barrier_vars_t barrier_vars;

static inline int spin_is_locked(void) {
        return (barrier_vars.barrier_lock != 0);
}

static inline int spin_trylock(void) {
	int tmp = 1, busy;

	__asm__ __volatile__ (
		"	amoswap.w %0, %2, %1\n"
		"       fence\n"
		: "=r" (busy), "+A" (barrier_vars.barrier_lock)
		: "r" (tmp)
		: "memory");

	return !busy;
}

static inline void spin_lock(void) {
	while (1) {
		if (spin_is_locked())
			continue;

		if (spin_trylock())
			break;
	}
}

static inline void spin_unlock(void) {
        __asm__ __volatile__ ("fence");
        barrier_vars.barrier_lock = 0;
}

void andes_barrier(unsigned int n) {
        if (n <= 1)
                return;
        spin_lock();
        if (barrier_vars.barrier_arrive_counter == 0) {
                spin_unlock();
                while (barrier_vars.barrier_leave_counter != 0);
                spin_lock();
                barrier_vars.barrier_flag = 0;
        }
        barrier_vars.barrier_arrive_counter++;
        if (barrier_vars.barrier_arrive_counter == n) {
                barrier_vars.barrier_arrive_counter = 0;
                barrier_vars.barrier_leave_counter = 0;
                __asm__ __volatile__ ("fence");
                barrier_vars.barrier_flag = 1;
        }
        spin_unlock();

        while (barrier_vars.barrier_flag == 0);
        spin_lock();
        barrier_vars.barrier_leave_counter++;
        if (barrier_vars.barrier_leave_counter == n)
                barrier_vars.barrier_leave_counter = 0;
        spin_unlock();
}
