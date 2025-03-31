#include <testutils.h>
#include <util.h>
#include <thread.h>
#include "../cycledelay.h"

#define CYCLE_DELAY 10000

int run_cycledelay(void *arg) {
    UNUSED(arg);

    testcase_init();
    test_cycledelay();
    return testcase_finalize();
}

int main() {
    testcase_init();

    // Launch cycledelay on worker cores
    for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
        thread_launch(i, run_cycledelay, NULL);
    }

    // run dhrystone on core 0
    test_cycledelay();

    CHECK_TRUE(thread_join_all() == TEST_SUCCESS);
    
    return testcase_finalize();
}
