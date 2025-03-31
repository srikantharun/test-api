#include "common.h"

#define CACHE_SIZE 64  // Define a reasonable cache size for testing

// Cache storage array, aligned to 64 bytes for consistency with linker script
__attribute__((aligned(64))) uint64_t cache[CACHE_SIZE];

// Function to simulate accessing memory and tracking cache hits
int access_memory(uint64_t address) {
    uint64_t index = (address / 64) % CACHE_SIZE; // Use block size to compute index for aligned address

    // Check if the address is already present in the cache
    if (cache[index] == address) {
        return 1;  // Cache hit
    } else {
        // Cache miss: Load the address into the cache
        cache[index] = address;
        return 0;  // Cache miss
    }
}

// Function to reset the cache to an invalid state
void reset_cache() {
    for (int i = 0; i < CACHE_SIZE; i++) {
        cache[i] = (uint64_t)-1;  // Set to an invalid address
    }
}

// Function to test cache hits under various scenarios
void test_cache_hits_scenarios() {
    int hits = 0;  // Counter for cache hits

    // Scenario 1: Sequential Access
    reset_cache();  // Clear cache before starting this test
    printf("Testing sequential access...\n");
    uint64_t base_address = 0x2000000000100000;
    for (int i = 0; i < CACHE_SIZE; i++) {
        uint64_t address = base_address + (i * 64);  // Sequential access aligned with cache lines

        // First access should result in a cache miss
        if (CHECK_TRUE(access_memory(address) == 0, "Expected cache miss on first access for address %llx", address)) {
            printf("Cache miss on first access for address %llx as expected.\n", address);
        } else {
            return;  // Exit on error
        }

        // Second access should result in a cache hit
        if (CHECK_TRUE(access_memory(address) == 1, "Expected cache hit on second access for address %llx", address)) {
            hits++;
            printf("Cache hit for address %llx as expected.\n", address);
        } else {
            return;  // Exit on error
        }
    }
    printf("Sequential access test completed with %d hits detected.\n", hits);

    // Scenario 2: Repeated Access to Same Address
    reset_cache();  // Clear cache before starting this test
    printf("Testing repeated access to the same address...\n");
    uint64_t repeated_address = 0x2000000000100000;  // Single address
    for (int i = 0; i < 5; i++) {
        // First access should result in a cache miss
        if (i == 0) {
            if (CHECK_TRUE(access_memory(repeated_address) == 0, "Expected cache miss on first access for address %llx", repeated_address)) {
                printf("Cache miss on first access for address %llx as expected.\n", repeated_address);
            } else {
                return;  // Exit on error
            }
        } else {
            // Subsequent accesses should result in cache hits
            if (CHECK_TRUE(access_memory(repeated_address) == 1, "Expected cache hit on repeated access for address %llx", repeated_address)) {
                hits++;
                printf("Cache hit for address %llx as expected.\n", repeated_address);
            } else {
                return;  // Exit on error
            }
        }
    }
    printf("Repeated access test completed with %d hits detected.\n", hits);

    // Scenario 3: Access Patterns with Alternating Addresses
    reset_cache();  // Clear cache before starting this test
    printf("Testing alternating access pattern...\n");
    uint64_t address1 = 0x2000000000100000;
    uint64_t address2 = 0x2000000000101000;  // Different address with the same cache index
    for (int i = 0; i < 4; i++) {
        // First access to each address should result in a miss
        if (i < 2) {
            if (CHECK_TRUE(access_memory(address1) == 0, "Expected cache miss for address %llx", address1)) {
                printf("Cache miss for address %llx as expected.\n", address1);
            } else {
                return;  // Exit on error
            }

            if (CHECK_TRUE(access_memory(address2) == 0, "Expected cache miss for address %llx", address2)) {
                printf("Cache miss for address %llx as expected.\n", address2);
            } else {
                return;  // Exit on error
            }
        } else {
            // Subsequent accesses should still result in cache misses due to eviction
            if (CHECK_TRUE(access_memory(address1) == 0, "Expected cache miss for address %llx due to eviction", address1)) {
                printf("Cache miss for address %llx due to eviction as expected.\n", address1);
            } else {
                return;  // Exit on error
            }

            if (CHECK_TRUE(access_memory(address2) == 0, "Expected cache miss for address %llx due to eviction", address2)) {
                printf("Cache miss for address %llx due to eviction as expected.\n", address2);
            } else {
                return;  // Exit on error
            }
        }
    }
    printf("Alternating access pattern test completed with %d hits detected.\n", hits);

    // Scenario 4: Confirm Cache Capacity Does Not Exceed Limits
    reset_cache();  // Clear cache before starting this test
    printf("Testing cache capacity limits...\n");
    uint64_t capacity_addresses[CACHE_SIZE + 2];  // More than cache capacity
    for (int i = 0; i < CACHE_SIZE + 2; i++) {
        capacity_addresses[i] = base_address + (i * 64);  // Access pattern with unique addresses
    }

    for (int i = 0; i < CACHE_SIZE + 2; i++) {
        // Initial accesses fill the cache up to its capacity, resulting in misses
        if (i < CACHE_SIZE) {
            if (CHECK_TRUE(access_memory(capacity_addresses[i]) == 0, "Expected cache miss for address %llx within capacity", capacity_addresses[i])) {
                printf("Cache miss for address %llx within capacity as expected.\n", capacity_addresses[i]);
            } else {
                return;  // Exit on error
            }
        } else {
            // Exceeding the cache capacity should cause the oldest entries to be evicted, resulting in misses again
            if (CHECK_TRUE(access_memory(capacity_addresses[i]) == 0, "Expected cache miss for address %llx exceeding capacity", capacity_addresses[i])) {
                printf("Cache miss for address %llx exceeding capacity as expected.\n", capacity_addresses[i]);
            } else {
                return;  // Exit on error
            }
        }
    }
    printf("Cache capacity limit test completed with %d hits detected.\n", hits);

    // Verify total hits count
    if (CHECK_EQUAL_INT(hits, 68, "Expected 68 hits but got %d", hits)) {
        printf("All cache hit tests passed.\n");  // Print success message
    } else {
        printf("Cache hit test failed. Expected 68 hits but got %d hits.\n", hits);  // Print failure message
    }
}

int main() {
    testcase_init();  // Initialize test counters
    printf("Running test: cache_hits_scenarios\n");
    initialize_registers();

    // Run detailed cache hit tests
    test_cache_hits_scenarios();

    return testcase_finalize();  // Exit with the overall test result
}
