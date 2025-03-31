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
// Only one CPU within the PVE0 cluster will trigger the DMA tasks
start_core(PVE_0_CLUSTER_0_CORE_0);
// Only one CPU within the PVE1 cluster will trigger the DMA tasks
start_core(PVE_1_CLUSTER_0_CORE_0);
CHECK_TRUE(wait_core(PVE_0_CLUSTER_0_CORE_0) == TEST_SUCCESS);
CHECK_TRUE(wait_core(PVE_1_CLUSTER_0_CORE_0) == TEST_SUCCESS);
disable_simple_multicore_printf(APU_CORE_5);

return testcase_finalize();
}

