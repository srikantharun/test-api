#include "test_address_space_memory/address_space_utils.h"

int main(void) {
    uint64_t running_core_id = r_mhartid();
    uintptr_t forbidden_addresses[140] = {0};

    // Initialization steps
    testcase_init();

    printf("=== AICORE_%lu started ===\n", running_core_id);

    uintptr_t base_addresses[] = {
        AICORE_0_SPM_BASE,
        AICORE_1_SPM_BASE,
        AICORE_2_SPM_BASE,
        AICORE_3_SPM_BASE,
        AICORE_4_SPM_BASE,
        AICORE_5_SPM_BASE,
        AICORE_6_SPM_BASE,
        AICORE_7_SPM_BASE,
        SYS_SPM_BASE
    };

    uintptr_t ranges[sizeof(base_addresses) / sizeof(base_addresses[0])][2];
    int num_ranges = sizeof(base_addresses) / sizeof(base_addresses[0]);

    for (int i = 0; i < num_ranges; i++) {
        ranges[i][0] = base_addresses[i];
        ranges[i][1] = base_addresses[i] + 0x1000; // Reserve 4KiB
    }

    populate_forbidden_addresses(forbidden_addresses, ranges, num_ranges);

    // seed configuration
    uint64_t seed_original = 0xa6009b56f74513df + running_core_id;
    uint64_t seed_increment = 0x2d346e84abb9d9dd + running_core_id;

    // Run the memory test
    test_memories(forbidden_addresses, seed_original, seed_increment);

    printf("=== AICORE_%lu stopped ===\n",running_core_id);

    return testcase_finalize();
}
