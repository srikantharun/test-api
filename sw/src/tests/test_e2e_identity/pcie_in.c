#include <asm.h>
#include <platform.h>
#include <testutils.h>
#include <barrier.h>

#include "pipeline.h"

extern pipeline_t *pipeline;

int pcie_in_cb(void *arg) {
    UNUSED(arg);

    printf("Starting PCIE IN stage\n");

    // Wait for all workers to be ready
    pipeline_wait(pipeline);

    while(1)
    {
        // Phase A - Calculations
        if (pipeline_wait(pipeline))
            break;
        printf("Hello from PCIE IN stage\n");

        // Phase B - Verification
        if (pipeline_wait(pipeline))
            break;
        printf("Verification PCIE IN\n");
    }

    printf("Bye from PCIE IN stage\n");

    return TEST_SUCCESS;
}
