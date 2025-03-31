#include <platform.h>
#include <testutils.h>
#include <multicore.h>
#include <thread.h>
#include <timer.h>
#include <printf.h>

#include "pipeline.h"

#define E2E_ITERATION_NUM 4
#define E2E_WORKER_NUM    (1 + 3 + HW_DEFINES_PVE_0_CORE_NUMBER + HW_DEFINES_PVE_1_CORE_NUMBER + HW_DEFINES_AICORE_MODULE_NUMBER)

#define E2E_PCIE_IN_HART_ID          APU_CORE_1
#define E2E_PCIE_OUT_HART_ID         APU_CORE_2
#define E2E_CODEC_HART_ID            APU_CORE_3
#define E2E_MULTICORE_PRINTF_HART_ID APU_CORE_5


extern int pcie_in_cb(void *arg);
extern int pcie_out_cb(void *arg);
extern int codec_cb(void *arg);

pipeline_t *pipeline = &(pipeline_t){0};

int main() {
    unsigned long cycles_before_barrier;
    unsigned long cycles_after_barrier;

    /* START E2E TEST */
    testcase_init();
    pipeline_init(pipeline, E2E_WORKER_NUM);

    enable_simple_multicore_printf(E2E_MULTICORE_PRINTF_HART_ID);

    // Start all workers
    thread_launch(E2E_PCIE_IN_HART_ID,  pcie_in_cb,  NULL);
    thread_launch(E2E_PCIE_OUT_HART_ID, pcie_out_cb, NULL);
    thread_launch(E2E_CODEC_HART_ID,    codec_cb,    NULL);
    // Preprocessor workers
    start_cores_pve0_available();
    // Postprocessor workers
    start_cores_pve1_available();
    // AI Core workers
    start_aicores_available();

    // Pipeline managing
    pipeline_start(pipeline);
    for(int i = 0; i < E2E_ITERATION_NUM; i++) {
        // Phase A - calculations
        pipeline_barrier(pipeline);
        cycles_before_barrier = read_cycles();

        // Phase B - verification
        pipeline_barrier(pipeline);
        cycles_after_barrier = read_cycles();
        printf("#%03d: Phase A took %d cycles.\n", i, cycles_after_barrier - cycles_before_barrier);
    }
    pipeline_stop(pipeline);

    // Wait for all threads
    CHECK_EQUAL_INT(TEST_SUCCESS, thread_join(E2E_CODEC_HART_ID));
    CHECK_EQUAL_INT(TEST_SUCCESS, thread_join(E2E_PCIE_OUT_HART_ID));
    CHECK_EQUAL_INT(TEST_SUCCESS, thread_join(E2E_PCIE_IN_HART_ID));
    CHECK_EQUAL_INT(TEST_SUCCESS, wait_cores_pve0());

    /* END TEST */
    return testcase_finalize();
}
