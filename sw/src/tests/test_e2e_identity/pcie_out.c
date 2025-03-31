#include <asm.h>
#include <platform.h>
#include <testutils.h>
#include <barrier.h>

#include "pipeline.h"

extern pipeline_t *pipeline;

int pcie_out_cb(void *arg) {
    UNUSED(arg);

    printf("Starting PCIE OUT stage\n");

    // Wait for all workers to be ready
    pipeline_wait(pipeline);

    while(1)
    {
        // Phase A - Calculations
        if (pipeline_wait(pipeline))
            break;
        printf("Hello from PCIE OUT stage\n");

        // Phase B - Verification
        if (pipeline_wait(pipeline))
            break;
        printf("Verification PCIE OUT\n");
    };

    printf("Bye from PCIE OUT stage\n");

    return TEST_SUCCESS;
}
