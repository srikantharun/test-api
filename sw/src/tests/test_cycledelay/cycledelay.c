#include "cycledelay.h"

void test_cycledelay() {
    uint64_t cycle_count = read_csr(mcycle);
    cycledelay(CYCLE_DELAY);
    uint64_t cycle_count_post = read_csr(mcycle);
    
    CHECK_TRUE(cycle_count_post > cycle_count + CYCLE_DELAY);
}
