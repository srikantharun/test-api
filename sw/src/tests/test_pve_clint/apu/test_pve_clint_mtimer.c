#include <multicore.h>
#include <platform.h>
#include <printf.h>
#include <testutils.h>

int main(void) {
    printf("*** start test_pve_clint_mtimer...\n");

    testcase_init();

    // test sequentially as the test overwrites MTIME, which cannot happen in parallel
    // TODO: Extend to PVE1 once available.
    for (uint64_t hartid = PVE_0_CLUSTER_0_CORE_0; hartid <= PVE_0_CLUSTER_3_CORE_1; hartid++) {
        printf("testing on hartid=%0d\n", hartid);
        start_core(hartid);
        CHECK_TRUE(wait_core(hartid) == 0, "test failed on hartid=%0d", hartid);
    }

    return testcase_finalize();
}
