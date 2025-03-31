#include <testutils.h>
#include <thread.h>
#include <util.h>

#include "dhrystone.h"

int dhrystone(void *arg) {
    UNUSED(arg);
    testcase_init();
    run_dhrystone_checks();
    return testcase_finalize();
}

int main() {
    testcase_init();

    // launch dhrystone on other cores (in parallel)
    for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
        thread_launch(i, dhrystone, NULL);
    }

    // run dhrystone on core 0
    run_dhrystone_checks();

    CHECK_TRUE(thread_join_all() == TEST_SUCCESS);

    return testcase_finalize();
}
