#include "crosscore.h"
#include <testutils.h>
#include <atomics.h>
#include <atomics_lrsc.h>


extern exclusive_access_t exclusive_access_vars;

int is_core_active(uint64_t i) {
    if (i <= APU_CORE_5) {
        if (i <= EXCLUSIVE_APU_CORE_NUM)
            return 1;
    } else if (i <= AI_CORE_7) {
        return 0;
    } else if (i <= PVE_0_CLUSTER_3_CORE_1) {
        if (i < PVE_0_CLUSTER_0_CORE_0 + EXCLUSIVE_PVE0_CORE_NUM)
            return 1;
    } else if (i <= PVE_1_CLUSTER_3_CORE_1) {
        if (i < PVE_1_CLUSTER_0_CORE_0 + EXCLUSIVE_PVE1_CORE_NUM)
            return 1;
    }
    return 0;
}

int barrier_thread_function(void* arg) {
    UNUSED(arg);
    
    uint64_t core_id = r_mhartid();
    
    for (uint32_t iter = 0; iter < NUM_ITERATIONS; iter++) {
        // BEFORE THE BARRIER
        exclusive_access_vars.before_barrier_counts[core_id] = atomic_fetch_add_lrsc(&(exclusive_access_vars.before_barrier_count), 1) + 1;

        for (uint32_t i = APU_CORE_0; i < NUM_CORES; i++) {
            if (i != core_id && is_core_active(i)) {
                if (exclusive_access_vars.before_barrier_counts[i] == exclusive_access_vars.before_barrier_counts[core_id]) {
                    exclusive_access_vars.assert = 1;
                }
            }
        }

        // THE BARRIER
        barrier_wait(&(exclusive_access_vars.test_barrier));

        // AFTER THE BARRIER
        exclusive_access_vars.after_barrier_counts[core_id] = atomic_fetch_add_lrsc(&(exclusive_access_vars.after_barrier_count), 1) + 1;

        for (uint32_t i = APU_CORE_0; i < NUM_CORES; i++) {
            if (i != core_id && is_core_active(i)) {
                if (exclusive_access_vars.after_barrier_counts[i] == exclusive_access_vars.after_barrier_counts[core_id]) {
                    exclusive_access_vars.assert = 1;
                }
            }
        }

        // ASSERRTION PROCESSING
        if (exclusive_access_vars.assert) {
            if (core_id == APU_CORE_0) {
                for (uint32_t i = APU_CORE_0; i < NUM_CORES; i++) {
                    if (is_core_active(i)) {
                        for (uint32_t j = i + 1; j < NUM_CORES; j++) {
                            if (is_core_active(j)) {
                                CHECK_TRUE(exclusive_access_vars.before_barrier_counts[i] != exclusive_access_vars.before_barrier_counts[j], "\nIter %u,\t a before duplicate (%d, %d) in cores %u and %u.\n", iter, exclusive_access_vars.before_barrier_counts[i], exclusive_access_vars.before_barrier_counts[j], i, j);
                                CHECK_TRUE(exclusive_access_vars.after_barrier_counts[i] != exclusive_access_vars.after_barrier_counts[j], "\nIter %u,\t an after duplicate (%d, %d) in cores %u and %u.\n", iter, exclusive_access_vars.after_barrier_counts[i], exclusive_access_vars.after_barrier_counts[j], i, j);
                            }
                        }
                    }
                }
            }
        }
    }
    return exclusive_access_vars.assert ? TEST_FAILURE : TEST_SUCCESS;
}
