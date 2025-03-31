#pragma once

typedef struct {
    volatile unsigned int barrier_arrive_counter;
    volatile unsigned int barrier_leave_counter;
    volatile unsigned int barrier_flag;
    volatile unsigned int barrier_lock;
} barrier_vars_t;

void andes_barrier(unsigned int n);
