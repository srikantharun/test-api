#include <testutils.h>
#include <thread.h>
#include <util.h>

#include "whetstone.h"

int whetstone(void *arg) {
    UNUSED(arg);
    testcase_init();
    run_whetstone_checks(1, 1);
    return testcase_finalize();
}

int main() {
    printf("*** test_whetstone starts...\n");
    testcase_init();

    // launch whetstone on other cores (in parallel)
    for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
        thread_launch(i, whetstone, NULL);
    }

    // run whetstone on core 0
    run_whetstone_checks(1, 1);

    CHECK_TRUE(thread_join_all() == TEST_SUCCESS);

    return testcase_finalize();
}
