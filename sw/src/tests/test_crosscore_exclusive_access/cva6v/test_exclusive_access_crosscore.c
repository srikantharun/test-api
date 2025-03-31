// Copyright (C) 2025, Andes Technology Corp. Confidential Proprietary

#include <platform.h>
#include <trap.h>
#include <testutils.h>
#include "../crosscore.h"


extern exclusive_access_t exclusive_access_vars;

int main() {
    testcase_init();

    uint64_t core_id = r_mhartid();
    if (core_id >= PVE_0_CLUSTER_0_CORE_0)
        LOG_DBG("*** Crosscore exclusive access test on a PVE!\n");
    else
        LOG_DBG("*** Crosscore exclusive access test on an AICORE!\n");

    CHECK_EQUAL_INT(TEST_SUCCESS, barrier_thread_function(NULL));

	return testcase_finalize();
}
