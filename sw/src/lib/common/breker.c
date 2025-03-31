#include <asm.h>
#include <platform.h>

uint64_t __attribute__((aligned(64), section(".breker"))) breker_c2tm[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,};
uint64_t __attribute__((aligned(64), section(".breker"))) breker_t2cm[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,};

uint64_t __attribute__((aligned(1024), section(".data"))) breker_ddr[1024];

void shutdown(void)
{
    exit(0);
}
