#include "common.h"

#define CACHE_SIZE 64  // Define a reasonable cache size for testing
#define STRIDE 16      // Define a stride value for access patterns

// Cache storage array, aligned to 64 bytes for consistency with linker script
__attribute__((aligned(64))) uint64_t cache[CACHE_SIZE];
uint8_t cache_valid[CACHE_SIZE];  // Array to track validity of cache lines
uint8_t cache_dirty[CACHE_SIZE];  // Array to track dirty state of cache lines

// Function to simulate accessing memory and tracking cache misses
int access_memory_for_miss(uint64_t address) {
    uint64_t index = address % CACHE_SIZE;

    // Check if the address is already in the cache and is valid
    if (cache[index] == address && cache_valid[index]) {
        if (cache_dirty[index]) {
            printf("Cache hit for address %llx, marked as dirty.\n", address);
        } else {
            printf("Cache hit for address %llx, marked as clean.\n", address);
        }
        return 0;  // Cache hit
    } else {
        // Cache miss, load the address into the cache
        cache[index] = address;
        cache_valid[index] = 1;  // Mark as valid
        cache_dirty[index] = 0;  // Mark as clean
        printf("Cache miss for address %llx, loading into cache.\n", address);
        return 1;  // Cache miss
    }
}

// Function to simulate a write operation and handle dirty state
void cache_write(uint64_t address) {
    uint64_t index = address % CACHE_SIZE;

    // If the address is already in the cache, mark it as dirty
    if (cache[index] == address && cache_valid[index]) {
        cache_dirty[index] = 1;  // Mark as dirty
        printf("Cache write for address %llx, marked as dirty.\n", address);
    } else {
        // Cache miss on write; load the address into the cache and mark as dirty
        printf("Cache miss for address %llx on write, loading and marking as dirty.\n", address);
        cache[index] = address;
        cache_valid[index] = 1;  // Mark as valid
        cache_dirty[index] = 1;  // Mark as dirty
    }
}

// Function to flush or invalidate a cache line (simulate behavior)
void flush_cache_line(uint64_t address) {
    uint64_t index = address % CACHE_SIZE;
    cache[index] = (uint64_t)-1;  // Invalidate the cache line
    cache_valid[index] = 0;  // Mark as invalid
    cache_dirty[index] = 0;  // Mark as clean
    printf("Flushed cache line for address %llx\n", address);
}

// Enhanced function to test cache behavior with various real-world scenarios
void test_cache_real_scenarios() {
    int misses = 0;  // Counter for cache misses

    // Scenario 1: Loop with Stride Access
    printf("Testing loop with stride access...\n");
    for (uint64_t addr = 0x2000000000100000; addr < 0x2000000000100000 + (CACHE_SIZE * STRIDE); addr += STRIDE) {
        // Expect a cache miss on each stride due to non-contiguous memory access
        if (CHECK_TRUE(access_memory_for_miss(addr) == 1, "Expected cache miss for address %llx with stride access", addr)) {
            misses++;
        }
    }
    printf("Stride access test completed with %d misses detected.\n", misses);

    // Scenario 2: Reversed Access
    printf("Testing reversed access pattern...\n");
    for (uint64_t addr = 0x2000000000100000 + (CACHE_SIZE * 64); addr >= 0x2000000000100000; addr -= 64) {
        // Expect a cache miss initially due to loading from end to start
        if (CHECK_TRUE(access_memory_for_miss(addr) == 1, "Expected cache miss for address %llx in reversed access", addr)) {
            misses++;
        }
    }
    printf("Reversed access test completed with %d misses detected.\n", misses);

    // Scenario 3: Mixed Read and Write Operations
    printf("Testing mixed read/write operations...\n");
    uint64_t test_addresses[] = {0x2000000000100000, 0x2000000000101000, 0x2000000000102000, 0x2000000000103000};
    for (int i = 0; i < 4; i++) {
        // Simulate write operation
        cache_write(test_addresses[i]);

        // Verify that the cache line is marked as dirty
        if (!CHECK_TRUE(cache_dirty[test_addresses[i] % CACHE_SIZE] == 1, "Cache line not marked as dirty after write for address %llx", test_addresses[i])) {
            printf("Unexpected clean cache line after write for address %llx. Cache index state: %llx, Valid: %d, Dirty: %d\n",
                   test_addresses[i], cache[test_addresses[i] % CACHE_SIZE], cache_valid[test_addresses[i] % CACHE_SIZE], cache_dirty[test_addresses[i] % CACHE_SIZE]);
        }

        // Simulate read operation
        int read_result = access_memory_for_miss(test_addresses[i]);
        // Verify that read operations after write result in a cache hit
        if (CHECK_TRUE(read_result == 0, "Expected cache hit for address %llx on read", test_addresses[i])) {
            printf("Cache hit for address %llx on read as expected.\n", test_addresses[i]);
        } else {
            printf("Unexpected cache miss for address %llx on read. Cache index state: %llx, Valid: %d, Dirty: %d\n",
                   test_addresses[i], cache[test_addresses[i] % CACHE_SIZE], cache_valid[test_addresses[i] % CACHE_SIZE], cache_dirty[test_addresses[i] % CACHE_SIZE]);
        }

        // Flush cache line to reset state for next iteration
        flush_cache_line(test_addresses[i]);
    }

    printf("Real scenarios tests completed with %d misses detected.\n", misses);
}

// Function to test cache misses with various patterns
void test_cache_misses() {
    uint64_t addresses[15] = {0x2000000000100000, 0x2000000000101000, 0x2000000000102000, 0x2000000000103000,
                              0x2000000000104000, 0x2000000000200000, 0x2000000000201000, 0x2000000000202000,
                              0x2000000000300000, 0x2000000000301000, 0x2000000000302000, 0x2000000000303000,
                              0x2000000000304000, 0x2000000000400000, 0x2000000000401000};  // Test addresses
    int misses = 0;  // Counter for cache misses

    // Initialize cache with invalid entries
    for (int i = 0; i < CACHE_SIZE; i++) {
        cache[i] = (uint64_t)-1;  // Set to an invalid address
    }

    // Access each address twice
    for (int i = 0; i < 15; i++) {
        // First access should result in a cache miss
        if (CHECK_TRUE(access_memory_for_miss(addresses[i]) == 1, "Expected cache miss on first access for address %llx", addresses[i])) {
            misses++;
            printf("Cache miss for address %llx\n", addresses[i]);
        } else {
            printf("Error: Expected cache miss on first access for address %llx\n", addresses[i]);
        }

        // Second access should result in a cache hit
        if (CHECK_TRUE(access_memory_for_miss(addresses[i]) == 0, "Expected cache hit on second access for address %llx", addresses[i])) {
            printf("Cache hit for address %llx\n", addresses[i]);
        } else {
            printf("Error: Expected cache hit on second access for address %llx\n", addresses[i]);
        }
    }

    // Verify the number of cache misses
    if (CHECK_EQUAL_INT(misses, 15, "Expected 15 cache misses but got %d", misses)) {
        printf("Cache miss test passed.\n");  // Print success message
    } else {
        printf("Cache miss test failed. Misses: %d\n", misses);  // Print failure message
    }
}

// Function to test corner cases and special cases for cache misses
void test_cache_miss_special_cases() {
    int misses = 0;  // Counter for cache misses

    // Test 1: Access an unaligned address
    uint64_t unaligned_address = 0x2000000000100001;  // Address that is not aligned
    // Expect a cache miss because address is unaligned and not previously loaded
    if (CHECK_TRUE(access_memory_for_miss(unaligned_address) == 1, "Expected cache miss for unaligned address %llx", unaligned_address)) {
        printf("Cache miss for unaligned address %llx\n", unaligned_address);
        misses++;
    } else {
        printf("Error: Expected cache miss for unaligned address %llx\n", unaligned_address);
    }

    // Test 2: Access an address at the boundary of cache size
    uint64_t boundary_address = 0x2000000000100FFF;  // Last address before a new cache line
    // Expect a cache miss because the address is at the boundary of cache size
    if (CHECK_TRUE(access_memory_for_miss(boundary_address) == 1, "Expected cache miss for boundary address %llx", boundary_address)) {
        printf("Cache miss for boundary address %llx\n", boundary_address);
        misses++;
    } else {
        printf("Error: Expected cache miss for boundary address %llx\n", boundary_address);
    }

    // Test 3: Access the maximum possible address within memory bounds
    uint64_t max_address = 0x200000000017FFFF;  // Assuming upper bound for this test scenario
    // Expect a cache miss because the address is at the maximum limit
    if (CHECK_TRUE(access_memory_for_miss(max_address) == 1, "Expected cache miss for maximum address %llx", max_address)) {
        printf("Cache miss for maximum address %llx\n", max_address);
        misses++;
    } else {
        printf("Error: Expected cache miss for maximum address %llx\n", max_address);
    }

    // Test 4: Access cache with addresses that may cause aliasing
    uint64_t aliasing_address1 = 0x2000000000100000;  // Address pattern known to cause aliasing issues
    uint64_t aliasing_address2 = 0x2000000000200000;  // Another address with the same index but different tag
    // Expect cache misses initially due to aliasing
    if (CHECK_TRUE(access_memory_for_miss(aliasing_address1) == 1, "Expected cache miss for aliasing address %llx", aliasing_address1)) {
        printf("Cache miss for aliasing address %llx\n", aliasing_address1);
    }
    if (CHECK_TRUE(access_memory_for_miss(aliasing_address2) == 1, "Expected cache miss for aliasing address %llx", aliasing_address2)) {
        printf("Cache miss for aliasing address %llx\n", aliasing_address2);
        misses++;
    } else {
        printf("Error: Unexpected cache hit for aliasing address %llx\n", aliasing_address2);
    }

    // Test 5: Access addresses that exceed cache capacity (Capacity Miss Test)
    uint64_t capacity_test_addresses[CACHE_SIZE + 5];
    for (int i = 0; i < CACHE_SIZE + 5; i++) {
        capacity_test_addresses[i] = 0x2000000000100000 + (i * 0x1000);  // Increment by cache block size
    }

    // Expect cache misses when accessing more addresses than cache can hold
    for (int i = 0; i < CACHE_SIZE + 5; i++) {
        if (CHECK_TRUE(access_memory_for_miss(capacity_test_addresses[i]) == 1, "Expected cache miss for address %llx due to capacity limit", capacity_test_addresses[i])) {
            misses++;
        }
    }
    printf("Capacity miss test completed with %d misses detected.\n", misses);

}

int main() {
    printf("Running test: cache_misses\n");
    testcase_init();  // Initialize test counters
    initialize_registers();

    // Run main cache miss tests
    test_cache_misses();

    // Run special and corner cases tests
    test_cache_miss_special_cases();

    // Run real-world cache scenario tests
    test_cache_real_scenarios();

    return testcase_finalize();  // Exit with the overall test result
}
