// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <clint.h>
#include <printf.h>
#include <stdint.h>
#include <testutils.h>

#define TIMER_PERIOD 500

static volatile uint64_t num_mtimer_triggered = 0;

void verify_mtime() {
    num_mtimer_triggered++;
}

int main() {
    testcase_init();

    {
        printf("checking mtime register read...\n");

        uint64_t t1, t2;
        t1 = clint_read_mtime();
        t2 = clint_read_mtime();

        CHECK_TRUE(t2 > t1, "MTIME register value is not increasing");
    }

    {
        printf("checking mtime register write...\n");

        uint64_t old_mtime = clint_read_mtime();
        uint64_t new_mtime = old_mtime + (1ULL << 32);
        
        clint_write_mtime(new_mtime);

        uint64_t readback = clint_read_mtime();
        CHECK_TRUE(readback > new_mtime, "MTIME register value was not updated after write");
    }

    {
        printf("checking timer interrupts...\n");

        CHECK_TRUE(num_mtimer_triggered == 0, "timer interrupt has fired before enabling");

        // 1. enable timer interrupt
        clint_enable_timer(TIMER_PERIOD);

        // 2. busy loop for timer period
        clint_delay_mtime_cycles(TIMER_PERIOD);

        // 3. check interrupt has fired at least once
        CHECK_TRUE(num_mtimer_triggered >= 1, "timer interrupt has not fired");

        // 4. disable timer interrupt
        clint_disable_timer();
        uint64_t num_mtimer_triggered_after_disable = num_mtimer_triggered;

        // 5. busy loop for twice the timer period
        clint_delay_mtime_cycles(2 * TIMER_PERIOD);

        // 6. check interrupt has not fired since
        CHECK_EQUAL_INT(
            num_mtimer_triggered_after_disable,
            num_mtimer_triggered,
            "timer interrupt fired after disabling"
        );
    }

    return testcase_finalize();
}
