#include <thread.h>
#include <asm.h>
#include <printf.h>
#include <plmt/drv_plmt.h>
#include <critical_section.h>
#include <interrupt.h>


#define PRINT_ITERATIONS 3

void verify_mtimer(void) {
  printf("PLMT interrupt enabled\n");
  plmtDisableInterrupt();
}

void enable_timer_interrupt(){
    /* Disable interrupts in general. */
    uint64_t key = arch_irq_lock();

    /* Enable plmt interrupt*/
    plmtSetupInterrupt(24000);

    /* Enable interrupts in general. */
    arch_irq_unlock(key);
}

// Thread function to test locking mechanism
int thread_function(void* arg) {
    UNUSED(arg);
    uint64_t id = r_mhartid();

    enable_timer_interrupt();

    for (int i = 0; i < PRINT_ITERATIONS; i++) {
        printf("Thread %d is printiiiiiiiiiiiiing\n", id);
    }
    return 0;
}

int main() {
    // Create threads
    for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
        thread_launch(i, thread_function, NULL);
    }

    thread_function(NULL);

    thread_join_all();

    return 0;
}
