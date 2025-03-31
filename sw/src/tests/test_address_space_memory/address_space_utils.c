#include "address_space_utils.h"

void mem_access_power_of_2_addresses(enum ReadWriteType rw_type, const struct MemoryRegion *mem,
                                     uint64_t seed, uintptr_t *forbidden_addresses) {
  if (!is_allowed_mem(mem)) {
    printf("memory not allowed (%s)\n", mem->name);
    return;
  }
  if (rw_type == WRITE) {
    mem_write_u64_power_of_2_addresses(mem->name, mem->base, mem->size, seed, forbidden_addresses);
  } else {
    mem_check_read_u64_power_of_2_addresses(mem->name, mem->base, mem->size, seed,
                                            forbidden_addresses);
  }
}

bool is_allowed_mem(const struct MemoryRegion *mem) {
  // mem needs to be read/write
  if ((!mem->w) || (!mem->r)) {
    return false;
  }
  return true;
}

void test_memories(uintptr_t *forbidden_addresses, uint64_t seed_original,
                   uint64_t seed_increment) {
  const struct MemoryRegion *mem;
  uint64_t seed;

  // Write phase
  mem = memory_regions;
  seed = seed_original;
  while (mem->name) {
    mem_access_power_of_2_addresses(WRITE, mem, seed, forbidden_addresses);
    seed += seed_increment;
    mem++;
  }

  // Read/Compare phase
  mem = memory_regions;
  seed = seed_original;
  while (mem->name) {
    mem_access_power_of_2_addresses(READ, mem, seed, forbidden_addresses);
    seed += seed_increment;
    mem++;
  }
}

void mem_access_power_of_2_addresses_with_dma(dma_type_e dma_type, char *dma_name,
                                              uintptr_t main_dma_addr, enum ReadWriteType rw_type,
                                              const struct MemoryRegion *mem, uint64_t seed,
                                              uintptr_t *forbidden_addresses) {
  // TODO: take connectivity matrix into account
  if (!is_allowed_mem(mem)) {
    printf("memory not allowed (%s)\n", mem->name);
    return;
  }
  if (rw_type == WRITE) {
    mem_write_dma_power_of_2_addresses(dma_type, dma_name, main_dma_addr, mem->name, mem->base,
                                       mem->size, seed, forbidden_addresses);
  } else {
    mem_check_read_dma_power_of_2_addresses(dma_type, dma_name, main_dma_addr, mem->name, mem->base,
                                            mem->size, seed, forbidden_addresses);
  }
}

// TODO: only working for SNPS DMA at the moment
void test_memories_with_dma(dma_type_e dma_type, char *dma_name, uintptr_t *forbidden_addresses,
                            uint64_t seed_original, uint64_t seed_increment) {
  const struct MemoryRegion *mem;
  uint64_t seed;
  uint64_t main_dma_src_addr;
  uint64_t main_dma_dst_addr;
  // put main DMA src and dst at 3/4 of DDR to avoid being in the way of the powers of 2
  uint64_t main_dma_src_addr_original = DDR_0_BASE + (DDR_0_SIZE / 4) * 3;
  uint64_t main_dma_dst_addr_original = DDR_1_BASE + (DDR_1_SIZE / 4) * 3;
  // 2048B: 32B DMA accesses times 64 optential address's bits
  uint64_t main_dma_src_addr_increment = 2048;

  // Write phase: main_dma_src -> mem
  main_dma_src_addr = main_dma_src_addr_original;
  mem = memory_regions;
  seed = seed_original;
  while (mem->name) {
    mem_access_power_of_2_addresses_with_dma(dma_type, dma_name, main_dma_src_addr, WRITE, mem,
                                             seed, forbidden_addresses);
    main_dma_src_addr += main_dma_src_addr_increment;
    seed += seed_increment;
    mem++;
  }

  // Read/Compare phase
  main_dma_dst_addr = main_dma_dst_addr_original;
  mem = memory_regions;
  seed = seed_original;
  while (mem->name) {
    mem_access_power_of_2_addresses_with_dma(dma_type, dma_name, main_dma_dst_addr, READ, mem, seed,
                                             forbidden_addresses);
    main_dma_dst_addr += main_dma_src_addr_increment;
    seed += seed_increment;
    mem++;
  }
}
