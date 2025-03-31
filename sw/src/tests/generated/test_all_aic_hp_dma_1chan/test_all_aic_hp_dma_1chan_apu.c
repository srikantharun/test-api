// AUTO GENERATED, DON'T MANUALLY EDIT!!
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Automatic generated test file
// Owner: scripts/trex

#include <trex/trex_utils.h>
#include <testutils.h>
#include <printf.h>
#include <memutils.h>
#include <trex/generated_data.h>
#include <platform.h>
#include <multicore.h>
#include <thread.h>
#include <pctl_utils.h>
int main() {

testcase_init();

enable_simple_multicore_printf(APU_CORE_5);

// Always unfence the SDMA modules
pctl_enable_module(SDMA_MODULE_0);
pctl_enable_module(SDMA_MODULE_1);

// Always unfence the L2
pctl_enable_l2();

// Start the AICORE and PVE CPUs
start_core(AI_CORE_0);
start_core(AI_CORE_1);
start_core(AI_CORE_2);
start_core(AI_CORE_3);
start_core(AI_CORE_4);
start_core(AI_CORE_5);
start_core(AI_CORE_6);
start_core(AI_CORE_7);
CHECK_TRUE(wait_core(AI_CORE_0) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_1) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_2) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_3) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_4) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_5) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_6) == TEST_SUCCESS);
CHECK_TRUE(wait_core(AI_CORE_7) == TEST_SUCCESS);
disable_simple_multicore_printf(APU_CORE_5);

return testcase_finalize();
}

