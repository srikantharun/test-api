#include <asm.h>
#include <platform.h>
#include <testutils.h>
#include <thread.h>
#include <util.h>

int thread_hartid(void *arg) {
    UNUSED(arg);

    uint64_t hartid = r_mhartid();
    printf("Hello from core %d!\r\n", hartid);
    return hartid;
}

int thread_testcase_pass(void *arg) {
    UNUSED(arg);
    testcase_init();
    CHECK_TRUE(1);
    return testcase_finalize();
}

int thread_testcase_fail(void *arg) {
    UNUSED(arg);
    testcase_init();
    CHECK_TRUE(0);
    return testcase_finalize();
}

int main() {
    testcase_init();

    // Test for correct return value.
    for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
        thread_launch(i, thread_hartid, NULL);
    }
    for (tid_t i = 1; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
        CHECK_EQUAL_INT((int)i, thread_join(i));
    }

    // Test that testcases are core-local.
    thread_launch(1, thread_testcase_pass, NULL);
    CHECK_EQUAL_INT(thread_join(1), TEST_SUCCESS);

    thread_launch(2, thread_testcase_fail, NULL);
    CHECK_EQUAL_INT(thread_join(2), TEST_FAILURE);

    thread_launch(2, thread_testcase_pass, NULL);
    thread_launch(1, thread_testcase_fail, NULL);
    CHECK_EQUAL_INT(thread_join(2), TEST_SUCCESS);
    CHECK_EQUAL_INT(thread_join(1), TEST_FAILURE);

    thread_launch(2, thread_testcase_pass, NULL);
    thread_launch(1, thread_testcase_fail, NULL);
    CHECK_TRUE(thread_join_all() != TEST_SUCCESS);

    return testcase_finalize();
}
