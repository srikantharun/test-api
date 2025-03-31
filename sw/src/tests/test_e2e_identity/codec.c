#include <asm.h>
#include <platform.h>
#include <testutils.h>
#include <barrier.h>

#include "pipeline.h"

extern pipeline_t *pipeline;

int codec_cb(void *arg) {
    UNUSED(arg);

    printf("Starting CODEC stage\n");

    // Wait for all workers to be ready
    pipeline_wait(pipeline);

    while(1)
    {
        // Phase A - Calculations
        if (pipeline_wait(pipeline))
            break;
        printf("Hello from CODEC stage\n");

        // Phase B - Verification
        if (pipeline_wait(pipeline))
            break;
        printf("Verification CODEC\n");
    };

    printf("Bye from CODEC stage\n");

    return TEST_SUCCESS;
}
