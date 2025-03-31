#include <timer.h>

static inline unsigned long long rdmcycle(void)
{
#if __riscv_xlen == 32
do {
        unsigned long hi = read_csr(mcycleh);
        unsigned long lo = read_csr(mcycle);

        if (hi == read_csr(mcycleh))
            return ((unsigned long long)hi << 32) | lo;
} while(1);
#else
    return (unsigned long long)read_csr(mcycle);
#endif
}

static inline uint64_t usec_to_tick(unsigned long usec)
{
    return usec * CORE_FREQUENCY_MHz;
}

void __attribute__((weak)) udelay(uint64_t usec) {
    uint64_t delay_cycles;

    delay_cycles = rdmcycle() + usec_to_tick(usec);
    while (rdmcycle() < delay_cycles+1);
                /*NOP*/
}

long time_us(void)
{
    return rdmcycle() / CORE_FREQUENCY_MHz;
}

void cycledelay(uint64_t cycles)
{
    uint64_t delay_cycles = rdmcycle() + cycles;

    while (rdmcycle() < delay_cycles + 1);
}


unsigned int get_timer(unsigned int base) {
    return time_us() / MSEC_TO_USEC - base;
}
