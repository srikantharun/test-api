// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <log.h>
#include <memutils.h>

typedef enum { WRITE, READ } access_type_e;

#define MAX_DATA_WIDTH_IN_BYTE 64
#define UINT64_ACCESS_SIZE_IN_BYTE 8
#define DMA_ACCESS_SIZE_IN_BYTE 32

static bool is_forbidden_address(uintptr_t address, uintptr_t *forbidden_addresses) {
  if (forbidden_addresses == NULL) {
    return false;
  }
  while (*forbidden_addresses != 0) {
    if (address == *forbidden_addresses) {
      return true;
    }
    forbidden_addresses++;
  }
  return false;
}

// first: access all 64b addresses until MAX_DATA_WIDTH_IN_BYTE,
// then: access powers of 2 addresses
static uint64_t get_next_addr_offset(uint64_t addr_offset, uint64_t offset_increment) {
  if (addr_offset < MAX_DATA_WIDTH_IN_BYTE) {
    addr_offset += offset_increment;
  } else {
    addr_offset = addr_offset << 1;
  }
  return addr_offset;
}

static void dma_snps_access(dma_type_e dma_type, char *dma_name, uintptr_t src_addr,
                            uintptr_t dst_addr) {
  // shamelessly stolen from TREX
  if (dma_type == SNPS) {
    uint64_t tf_size_0[] = {DMA_ACCESS_SIZE_IN_BYTE}; // 32B is the minimal size
    uint64_t num_channels_0 = 1;
    uint64_t dmac_ch_num_0[] = {0};
    uint64_t cfg_flags_0[] = {CH_CFG_SRC_OSR_LMT(15) | CH_CFG_DST_OSR_LMT(15) | CH_CFG_WR_UID(4) |
                              CH_CFG_RD_UID(4)};
    uint64_t ctl_flags_0[] = {CH_CTL_AWLEN_EN | CH_CTL_ARLEN_EN | CH_CTL_AWLEN(64) |
                              CH_CTL_ARLEN(64)};
    uintptr_t src_0[] = {src_addr};
    uintptr_t dst_0[] = {dst_addr};
    bool verbose = false;
    test_snps_dma_multi_channel_sel("memutils", (snps_dmac_regs *)get_dma_base_addr(dma_name),
                                    num_channels_0, dmac_ch_num_0, src_0, dst_0, ctl_flags_0,
                                    cfg_flags_0, tf_size_0, verbose);
  } else {
    ASSERT(0, "unsupported dma_type");
  }
}

static void mem_access_u64_power_of_2_addresses(access_type_e access_type, const char *mem_name,
                                                uintptr_t addr_base, uint64_t addr_size,
                                                uint64_t (*addr_interleaving_cb)(uint64_t),
                                                uint64_t seed, uintptr_t *forbidden_addresses) {
  uint64_t addr_offset = 0;
  while (1) {
    uint64_t *p_address;
    uint64_t wdata;

    // exit condition
    if (addr_offset >= addr_size) {
      break;
    }

    // compute address
    if (addr_interleaving_cb != NULL) {
      p_address = (uint64_t *)(addr_interleaving_cb(addr_base + addr_offset));
    } else {
      p_address = (uint64_t *)(addr_base + addr_offset);
    }

    // compute next address offset
    addr_offset = get_next_addr_offset(addr_offset, UINT64_ACCESS_SIZE_IN_BYTE);

    // skip forbidden addresses
    if (is_forbidden_address((uintptr_t)p_address, forbidden_addresses)) {
      LOG_WRN("skip forbidden address [0x%010lx]", (uint64_t)p_address);
      continue;
    }

    // access
    wdata = xorshift64(&seed);
    if (access_type == READ) {
      uint64_t rdata = *p_address;
      printf("0x%016lx <- [0x%010lx] (%s)\n", rdata, (uint64_t)p_address, mem_name);
      if (!CHECK_EQUAL_HEX(wdata, rdata)) {
        printf("ERROR: at address 0x%010lx\n", (uint64_t)p_address);
      }
    } else {
      printf("0x%016lx -> [0x%010lx] (%s)\n", wdata, (uint64_t)p_address, mem_name);
      *p_address = wdata;
    }
  }
}

// access memory's power of 2 addresses with the DMA, `dma_src/dst` is accessed in a contiguous
// manner,
//   WRITE: `dma_src -> mem`
//   READ: `dma_dst <- mem`
static void mem_access_dma_power_of_2_addresses(access_type_e access_type, dma_type_e dma_type,
                                                char *dma_name, uintptr_t dma_src_or_dst_addr_base,
                                                const char *mem_name, uintptr_t addr_base,
                                                uint64_t addr_size, uint64_t seed,
                                                uintptr_t *forbidden_addresses) {

  uint64_t addr_offset = 0;
  uint64_t dma_src_or_dst_addr_offset = 0;
  while (1) {
    uint64_t *p_address;
    uint64_t *p_dma_src_or_dst_addr;
    uint64_t forbidden_address_found = 0;

    // exit condition
    if (addr_offset >= addr_size) {
      break;
    }

    // compute address
    // TODO: support for interleaving cb
    p_address = (uint64_t *)(addr_base + addr_offset);
    for (uint64_t i = 0; i < (DMA_ACCESS_SIZE_IN_BYTE / UINT64_ACCESS_SIZE_IN_BYTE); i++) {
      if (is_forbidden_address((uintptr_t)(p_address + i), forbidden_addresses)) {
        forbidden_address_found = 1;
        break;
      }
    }
    p_dma_src_or_dst_addr = (uint64_t *)(dma_src_or_dst_addr_base + dma_src_or_dst_addr_offset);

    // compute next address offset
    addr_offset = get_next_addr_offset(addr_offset, DMA_ACCESS_SIZE_IN_BYTE);
    dma_src_or_dst_addr_offset += DMA_ACCESS_SIZE_IN_BYTE;

    // skip forbidden addresses
    if (forbidden_address_found) {
      LOG_WRN("skip forbidden address [0x%010lx]", (uint64_t)p_address);
      continue;
    }

    if (access_type == WRITE) { // dma_src -> mem
      // CPU populate dma_src
      for (uint64_t i = 0; i < (DMA_ACCESS_SIZE_IN_BYTE / UINT64_ACCESS_SIZE_IN_BYTE); i++) {
        uint64_t wdata = xorshift64(&seed);
        *(p_dma_src_or_dst_addr + i) = wdata;
      }

      // DMA access
      printf("DMA src[0x%010lx] -> dst[0x%010lx] (%s)\n", (uint64_t)p_dma_src_or_dst_addr,
             (uint64_t)p_address, mem_name);
      dma_snps_access(dma_type, dma_name, (uintptr_t)p_dma_src_or_dst_addr, (uintptr_t)p_address);
    } else { // mem -> dma_dst
      // DMA access
      printf("DMA dst[0x%010lx] <- src[0x%010lx] (%s)\n", (uint64_t)p_dma_src_or_dst_addr,
             (uint64_t)p_address, mem_name);
      dma_snps_access(dma_type, dma_name, (uintptr_t)p_address, (uintptr_t)p_dma_src_or_dst_addr);

      // CPU check dma_dst
      for (uint64_t i = 0; i < (DMA_ACCESS_SIZE_IN_BYTE / UINT64_ACCESS_SIZE_IN_BYTE); i++) {
        uint64_t wdata = xorshift64(&seed);
        uint64_t rdata = *(p_dma_src_or_dst_addr + i);
        if (!CHECK_EQUAL_HEX(wdata, rdata)) {
          printf("ERROR: at address 0x%010lx\n", (uint64_t)(p_dma_src_or_dst_addr + i));
        }
      }
    }
  }
}

void populate_forbidden_addresses(uintptr_t *forbidden_addresses, uintptr_t ranges[][2],
                                  int num_ranges) {
  int index = 0;

  for (int range_idx = 0; range_idx < num_ranges; range_idx++) {
    uintptr_t start = ranges[range_idx][0];
    uintptr_t end = ranges[range_idx][1];
    uint64_t addr_offset = 0;

    // see mem_access_u64_power_of_2_addresses function
    while (1) {
      uint64_t addr;
      addr = start + addr_offset;

      if (addr > end) {
        break;
      }

      // compute next address offset
      addr_offset = get_next_addr_offset(addr_offset, UINT64_ACCESS_SIZE_IN_BYTE);

      forbidden_addresses[index++] = addr;
    }

    // Ensure the end address is included if aligned
    if (forbidden_addresses[index - 1] != end) {
      forbidden_addresses[index++] = end;
    }
  }
}

void mem_write_u64_power_of_2_addresses(const char *mem_name, uintptr_t addr_base,
                                        uint64_t addr_size, uint64_t seed,
                                        uintptr_t *forbidden_addresses) {
  mem_access_u64_power_of_2_addresses(WRITE, mem_name, addr_base, addr_size, NULL, seed,
                                      forbidden_addresses);
}

void mem_check_read_u64_power_of_2_addresses(const char *mem_name, uintptr_t addr_base,
                                             uint64_t addr_size, uint64_t seed,
                                             uintptr_t *forbidden_addresses) {
  mem_access_u64_power_of_2_addresses(READ, mem_name, addr_base, addr_size, NULL, seed,
                                      forbidden_addresses);
}

void mem_write_u64_power_of_2_addresses_with_interleaving(
    const char *mem_name, uintptr_t addr_base, uint64_t addr_size,
    uint64_t (*addr_interleaving_cb)(uint64_t), uint64_t seed, uintptr_t *forbidden_addresses) {
  mem_access_u64_power_of_2_addresses(WRITE, mem_name, addr_base, addr_size, addr_interleaving_cb,
                                      seed, forbidden_addresses);
}

void mem_check_read_u64_power_of_2_addresses_with_interleaving(
    const char *mem_name, uintptr_t addr_base, uint64_t addr_size,
    uint64_t (*addr_interleaving_cb)(uint64_t), uint64_t seed, uintptr_t *forbidden_addresses) {
  mem_access_u64_power_of_2_addresses(READ, mem_name, addr_base, addr_size, addr_interleaving_cb,
                                      seed, forbidden_addresses);
}

void mem_write_dma_power_of_2_addresses(dma_type_e dma_type, char *dma_name,
                                        uintptr_t dma_src_addr_base, const char *mem_name,
                                        uintptr_t addr_base, uint64_t addr_size, uint64_t seed,
                                        uintptr_t *forbidden_addresses) {
  mem_access_dma_power_of_2_addresses(WRITE, dma_type, dma_name, dma_src_addr_base, mem_name,
                                      addr_base, addr_size, seed, forbidden_addresses);
}

void mem_check_read_dma_power_of_2_addresses(dma_type_e dma_type, char *dma_name,
                                             uintptr_t dma_dst_addr_base, const char *mem_name,
                                             uintptr_t addr_base, uint64_t addr_size, uint64_t seed,
                                             uintptr_t *forbidden_addresses) {
  mem_access_dma_power_of_2_addresses(READ, dma_type, dma_name, dma_dst_addr_base, mem_name,
                                      addr_base, addr_size, seed, forbidden_addresses);
}

// Compare memory and provide useful log
// x and y must be aligned to 8 bytes, n_bytes and offset must be multiple of 8
void mem_check_equal(const char *x, const char *y, int offset, int n_bytes, const char *msg) {
  int end_offset = offset + n_bytes;
  int mem_equal = 1;
  int n_prints_left = 2; // control number of 8B blocks printed in case of error here
  while (offset < end_offset) {
    uint64_t ix = *(uint64_t *)(x + offset);
    uint64_t iy = *(uint64_t *)(y + offset);
    if (ix != iy) {
      if (mem_equal) {
        printf("[CHECK FAILED] Memory different (%s)\n", msg);
        mem_equal = 0;
      }
      if (n_prints_left) {
        printf(" | %5d : %016lx -> %016lx\n", offset, ix, iy);
        n_prints_left--;
      }
    }
    offset += 8;
  }
}
