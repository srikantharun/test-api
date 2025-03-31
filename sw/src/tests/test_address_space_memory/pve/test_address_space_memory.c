#include "test_address_space_memory/address_space_utils.h"

int main(void) {
    uint64_t running_core_id = r_mhartid();
    uintptr_t forbidden_addresses[20] = {0};

    // Initialization steps
    testcase_init();

    printf("=== PVE_%lu started ===\n", running_core_id);

    uintptr_t ranges[2][2];

    if(running_core_id >= PVE_0_CLUSTER_0_CORE_0 && running_core_id <= PVE_0_CLUSTER_3_CORE_1){
      // Keep first 4KiB out of 128KiB for code and data
      ranges[0][0] = PVE_0_SPM_BASE;
      ranges[0][1] = PVE_0_SPM_BASE + 0x1000;
    }
    else{
       // Keep first 4KiB out of 128KiB for code and data
      ranges[0][0] = PVE_1_SPM_BASE;
      ranges[0][1] = PVE_1_SPM_BASE + 0x1000;
    }

    // Keep first 16KiB of SYS_SPM untouched
    ranges[1][0] = SYS_SPM_BASE;
    ranges[1][1] = SYS_SPM_BASE + 0x4000;

    int num_ranges = sizeof(ranges) / sizeof(ranges[0]);
    populate_forbidden_addresses(forbidden_addresses, ranges, num_ranges);

    // seed configuration
    uint64_t seed_original = 0xa6009b56f74513df + running_core_id;
    uint64_t seed_increment = 0x2d346e84abb9d9dd + running_core_id;

    // Run the memory test
    test_memories(forbidden_addresses, seed_original, seed_increment);

    printf("=== PVE_%lu stopped ===\n",running_core_id);

    return testcase_finalize();
}
