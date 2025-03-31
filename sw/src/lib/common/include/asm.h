// RISC-V assembly function wrappers
#pragma once

#include <stdint.h>
#include <hartids.h>

static inline uint64_t r_mhartid() {
    uint64_t id;
    asm("csrr %0, mhartid" : "=r" (id));
    return id;
}

#ifdef SYSTEM_TOP

extern volatile uint64_t stack_addrs[NUM_CORES];
extern void* _stack_begin;

static inline uint64_t r_uhartid() {
    void* sp;
    asm volatile("mv %0, sp" : "=r"(sp));  // Read the stack pointer into sp

    for(int i = 0; i<NUM_CORES; i++)
    {
        if((uint64_t*)sp < (uint64_t*)stack_addrs[i]){
            return i;
        }
    }
    return 0xFFFFFFFF;
}

#else

static inline uint64_t r_uhartid() {
    return r_mhartid();
}

#endif
