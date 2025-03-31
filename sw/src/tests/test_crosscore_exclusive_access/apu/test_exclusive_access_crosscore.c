// Copyright (C) 2025, Andes Technology Corp. Confidential Proprietary

#include <platform.h>
#include <trap.h>
#include <interrupt.h>
#include <thread.h>
#include <multicore.h>
#include <testutils.h>
#include <atomics_lrsc.h>
#include "../crosscore.h"


exclusive_access_t __attribute__((section(".sys_spm"))) exclusive_access_vars = {
    .before_barrier_count = 0,
    .after_barrier_count = 0,
    .before_barrier_counts = {0},
    .after_barrier_counts = {0},
    .assert = 0
};

void except_handler(SAVED_CONTEXT* context) {
	unsigned int misa;

    context->mepc += 4;

    context->x10 = read_csr(NDS_MHARTID);

    misa = read_csr(NDS_MISA);
    CHECK_TRUE(misa & 0x1, "RISC-V Atomic Instruction Extension is not set properly.");

	if ((misa & 0x1) == 0) {
		printf("'RISC-V Atomic Instruction Extension' should be configured to run this test.\n");
        exit(TEST_FAILURE);
	}
}

int main() {
    testcase_init();

    /* TEST START */
    enable_simple_multicore_printf(APU_CORE_5);
    barrier_init(&(exclusive_access_vars.test_barrier), EXCLUSIVE_CORE_NUM);

    /* Start cores */
    for(uint32_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id < PVE_0_CLUSTER_0_CORE_0 + EXCLUSIVE_PVE0_CORE_NUM; core_id ++)
        start_core(core_id);
    for(uint32_t core_id = PVE_1_CLUSTER_0_CORE_0; core_id < PVE_1_CLUSTER_0_CORE_0 + EXCLUSIVE_PVE1_CORE_NUM; core_id ++)
        start_core(core_id);
    for(uint32_t core_id = AI_CORE_0; core_id < AI_CORE_0 + EXCLUSIVE_AICORE_NUM; core_id ++)
        start_core(core_id);
    
    for (uint32_t i = APU_CORE_1; i < EXCLUSIVE_APU_CORE_NUM; i++)
        thread_launch((tid_t)i, barrier_thread_function, NULL);

    /* APU */
    if (EXCLUSIVE_APU_CORE_NUM >= 1)
        CHECK_EQUAL_INT(TEST_SUCCESS, barrier_thread_function(NULL));

    /* Checks */
    for(uint32_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id < PVE_0_CLUSTER_0_CORE_0 + EXCLUSIVE_PVE0_CORE_NUM; core_id ++)
        CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(core_id));
    for(uint32_t core_id = PVE_1_CLUSTER_0_CORE_0; core_id < PVE_1_CLUSTER_0_CORE_0 + EXCLUSIVE_PVE1_CORE_NUM; core_id ++)
        CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(core_id));
    for(uint32_t core_id = AI_CORE_0; core_id < AI_CORE_0 + EXCLUSIVE_AICORE_NUM; core_id ++)
        CHECK_EQUAL_INT(TEST_SUCCESS, wait_core(core_id));
    for (uint32_t i = APU_CORE_1; i < EXCLUSIVE_APU_CORE_NUM; i++)
        CHECK_EQUAL_INT(TEST_SUCCESS, thread_join((tid_t)i));

    // Check if all threads reached the barrier
    CHECK_EQUAL_INT(EXCLUSIVE_CORE_NUM * NUM_ITERATIONS, exclusive_access_vars.before_barrier_count, "Not all threads reached the barrier.");
    CHECK_EQUAL_INT(EXCLUSIVE_CORE_NUM * NUM_ITERATIONS, exclusive_access_vars.after_barrier_count, "Not all threads passed the barrier.");

    /* TEST END */
	return testcase_finalize();
}
