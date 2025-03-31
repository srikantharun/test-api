#include <asm.h>
#include <platform.h>
#include <testutils.h>
#include <barrier.h>
#include <printf.h>

#include "pipeline.h"

extern pipeline_t *pipeline;

int main() {
    uint64_t core_offset = r_mhartid() - processor_first_hart_id();
    printf("Starting AI Core stage %lu\n", core_offset);

    // Wait for all workers to be ready
    pipeline_wait(pipeline);

    while(1)
    {
        // Phase A - Calculations
        if (pipeline_wait(pipeline))
            break;
        printf("Hello from AI Core stage %lu\n", core_offset);

        // Phase B - Verification
        if (pipeline_wait(pipeline))
            break;
        printf("Verification of AI Core stage %lu\n", core_offset);
    };

    printf("Bye from AI Core stage %lu\n", core_offset);

    return TEST_SUCCESS;
}
