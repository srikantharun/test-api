// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Infinite sparse, simulation memory. Can be accessed via `dpi`
// calls in simulation.
// Owner: Florian Zaruba <florian.zaruba@axelera.ai>

#include <svdpi.h>

#include <iomanip>
#include <iostream>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>
#include <fstream>

#include "elfloader.hh"

namespace raptor {

/// A global memory.
struct GlobalMemory {
  static constexpr size_t ADDR_SHIFT = 12;
  static constexpr size_t PAGE_SIZE  = (size_t)1 << ADDR_SHIFT;

  std::unordered_map<uint64_t, std::unique_ptr<uint8_t[]>> pages;
  std::set<uint64_t>                                       touched;
  bool init_mem = true;

  // A mapping of host memory into Raptor memory.
  struct Mapping {
    uint64_t base;  // Raptor memory
    size_t   size;
    uint8_t *into;  // host memory
  };
  std::vector<Mapping> mappings;

  uint8_t *find_mapping(uint64_t addr) const {
    for (const auto &m : mappings) {
      if (m.base <= addr && m.base + m.size > addr) {
        return m.into + (addr - m.base);
      }
    }
    return nullptr;
  }

  // Copy a chunk of data into memory.
  void write(size_t addr, size_t len, const uint8_t *data, const uint8_t *strb) {
    size_t end      = addr + len;
    size_t data_idx = 0;

    std::ofstream file;

    if (init_mem) {
      file.open("c_mem.log");
      init_mem = false;
    } else {
      file.open("c_mem.log", std::ios::app);
    }

    // Redirect std::cout to the file stream
    std::streambuf *coutbuf = std::cout.rdbuf(); // Save old buf
    std::cout.rdbuf(file.rdbuf()); // Redirect std::cout to file

    while (addr < end) {
      size_t byte_start = addr;
      addr              >>= ADDR_SHIFT;
      auto    &page     = pages[addr];
      uint64_t page_idx = addr;
      if (!page) {
        std::cout << "[raptor.write] Allocate page " << std::hex << (addr << ADDR_SHIFT) << "\n";
        page = std::make_unique<uint8_t[]>(PAGE_SIZE);
        std::fill(&page[0], &page[PAGE_SIZE], 0);
      }
      std::cout << "[raptor.write] Write to page " << std::hex << (addr << ADDR_SHIFT) << "\n";
      addr               += 1;
      addr               <<= ADDR_SHIFT;
      size_t byte_end    = std::min(addr, end);
      bool   any_changed = false;
      for (size_t i = byte_start; i < byte_end; i++, data_idx++) {
        if (!strb || strb[data_idx]) {
          std::cout << "[raptor.write] Write byte " << std::hex << i << " = " << (uint32_t)data[data_idx] << "\n";
          auto host = find_mapping(i);
          if (host) {
            *host = data[data_idx];
          } else {
            page[i % PAGE_SIZE] = data[data_idx];
            any_changed         = true;
          }
        }
      }
      if (any_changed) touched.insert(page_idx);
    }
    std::cout << std::dec;
    // Restore std::cout
    std::cout.rdbuf(coutbuf); // Restore old buf
  }

  // Copy a chunk of data out of the memory.
  void read(size_t addr, size_t len, uint8_t *data) {
    size_t end      = addr + len;
    size_t data_idx = 0;

    std::ofstream file;

    if (init_mem) {
      file.open("c_mem.log");
      init_mem = false;
    } else {
      file.open("c_mem.log", std::ios::app);
    }

    // Redirect std::cout to the file stream
    std::streambuf *coutbuf = std::cout.rdbuf(); // Save old buf
    std::cout.rdbuf(file.rdbuf()); // Redirect std::cout to file

    while (addr < end) {
      size_t byte_start = addr;
      addr              >>= ADDR_SHIFT;
      auto &page        = pages[addr];
      std::cout << "[raptor.read] Read from page " << std::hex << (addr << ADDR_SHIFT) << "\n";
      addr              += 1;
      addr              <<= ADDR_SHIFT;
      size_t byte_end   = std::min(addr, end);
      for (size_t i = byte_start; i < byte_end; i++, data_idx++) {
        auto host = find_mapping(i);
        if (host) {
          data[data_idx] = *host;
        } else {
          if (page) {
            std::cout << "[raptor.read] Read byte " << std::hex << i << "\n";
            data[data_idx] = page[i % PAGE_SIZE];
          } else {
            data[data_idx] = 0;
          }
        }
      }
    }
    std::cout << std::dec;
    // Restore std::cout
    std::cout.rdbuf(coutbuf); // Restore old buf
  }
};

// The global memory all memory ports write into.
GlobalMemory MEM;
/// The entry point of the most recently loaded binary.
uint64_t     entry = 0x800000000;

/// Load an ELF binary.
static void load_binary(ElfBinary &bin) {
  entry = bin.entry;
  std::cout << "[load_binary] Loading " << bin.sections.size() << " sections\n";
  for (const auto &section : bin.sections) {
    std::cout << "[load_binary] Loading section at " << std::hex << section.data_dst << std::dec << " (" << section.data_len
              << " bytes, " << section.zero_len << " bytes padding)\n";
    auto zero = std::make_unique<uint8_t[]>(section.zero_len);
    std::fill(&zero[0], &zero[section.zero_len], 0);
    MEM.write(section.data_dst, section.data_len, section.data_src, nullptr);
    MEM.write(section.zero_dst, section.zero_len, zero.get(), nullptr);
  }
}
}  // namespace raptor

extern "C" {

/// Load a binary from a file.
void load_binary_file(const char *filename) {
  std::cout << "[load_binary_file] Loading binary " << filename << "\n";
  ElfBinaryFile bin(filename);
  raptor::load_binary(bin);
}

void tb_memory_read(long long addr, int len, const svOpenArrayHandle data) {
  // std::cout << "[tb_memory_read] Read " << std::hex << addr << std::dec << " (" << len << " bytes)\n";
  void *data_ptr = svGetArrayPtr(data);
  assert(data_ptr);
  raptor::MEM.read(addr, len, (uint8_t *)data_ptr);
}

void tb_memory_write(long long addr, int len, const svOpenArrayHandle data, const svOpenArrayHandle strb) {
  // std::cout << "[tb_memory_write] Write " << std::hex << addr << std::dec << " (" << len << " bytes)\n";
  const void *data_ptr = svGetArrayPtr(data);
  const void *strb_ptr = svGetArrayPtr(strb);
  assert(data_ptr);
  assert(strb_ptr);
  raptor::MEM.write(addr, len, (const uint8_t *)data_ptr, (const uint8_t *)strb_ptr);
}
}
