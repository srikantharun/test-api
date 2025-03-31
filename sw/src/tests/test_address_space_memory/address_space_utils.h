#include "hw_defines.h"
#include "memories.h"
#include <asm.h>
#include <memorymap.h>
#include <memutils.h>
#include <stdbool.h>
#include <testutils.h>

enum ReadWriteType {
  READ,
  WRITE,
};

void mem_access_power_of_2_addresses(enum ReadWriteType rw_type, const struct MemoryRegion *mem,
                                     uint64_t seed, uintptr_t *forbidden_addresses);

void mem_access_power_of_2_addresses_with_dma(dma_type_e dma_type, char *dma_name,
                                              uintptr_t main_dma_src_addr,
                                              enum ReadWriteType rw_type,
                                              const struct MemoryRegion *mem, uint64_t seed,
                                              uintptr_t *forbidden_addresses);

bool is_allowed_mem(const struct MemoryRegion *mem);

void test_memories(uintptr_t *forbidden_addresses, uint64_t seed_original, uint64_t seed_increment);

void test_memories_with_dma(dma_type_e dma_type, char *dma_name, uintptr_t *forbidden_addresses,
                            uint64_t seed_original, uint64_t seed_increment);
