#include "preloaded_sim.h"
#include <common/include/memorymap.h>
#include <filesystem>
#include <sim.h>
#include <string>
#include <vector>

using namespace std;

bool preloaded_sim_t::is_address_preloaded(addr_t addr, size_t size) {
  for (auto &device : device_list) {
    if (!device->is_preloaded()) {
      continue;
    }
    if ((addr >= device->base_addr()) &&
        ((addr + size) < (device->base_addr() + device->size()))) {
      return true;
    }
  }
  return false;
}

static std::vector<char> create_rom() {
  // Without `dtb` support we need to manually create a bootloader.
  //
  // Originates from riscv-isa-sim/riscv/sim.cc: void sim_t::set_rom()
  const int reset_vec_size = 8;

  uint64_t start_pc = SYS_SPM_BASE;

  uint32_t reset_vec[reset_vec_size] = {
      0x297,                                // auipc  t0,0x0
      0x28593 + (reset_vec_size * 4 << 20), // addi   a1, t0, &dtb
      0xf1402573,                           // csrr   a0, mhartid
#if ARCH == 32
      0x0182a283u // lw     t0,24(t0)
#else
      0x0182b283u, // ld     t0,24(t0)
#endif
      0x28067, // jr     t0
      0,
      (uint32_t)(start_pc & 0xffffffff),
      (uint32_t)(start_pc >> 32)};

  std::vector<char> rom((char *)reset_vec,
                        (char *)reset_vec + sizeof(reset_vec));
  return rom;
}

int run_sim(string elf, vector<pair<reg_t, mem_t *>> mems,
            vector<pair<reg_t, abstract_device_t *>> plugin_devices) {

  std::pair<reg_t, reg_t> initrd_bounds = std::make_pair((reg_t)0, (reg_t)0);
  char *bootargs = nullptr;
  char const *isa = "rv64gcv";
  char const *priv = DEFAULT_PRIV;
  char const *varch = DEFAULT_VARCH;
  bool misaligned = false;
  endianness_t endianness = endianness_little;
  reg_t pmpregions = 16;
  reg_t pmpgranularity = (1 << PMP_SHIFT);
  std::vector<mem_cfg_t> mem_layout; // No layout needed, memories are added
                                     // through argument 'mems'
  std::vector<size_t> hartids = {0};
  bool real_time_clint = false;
  bool trigger_count = 4;
  cfg_t cfg(initrd_bounds, bootargs, isa, priv, varch, misaligned, endianness,
            pmpregions, mem_layout, hartids, real_time_clint, trigger_count);

  std::vector<std::string> htif_args{elf};
  debug_module_config_t dm_config;

#ifdef DUMP_INST
  std::filesystem::path dump_path(elf);
  dump_path = dump_path.replace_filename("instruction_dump_ax65_id0.log");
  const char *dump_ptr = dump_path.c_str();
#else
  char *dump_ptr = nullptr;
#endif

  rom_device_t boot_rom(create_rom());
  plugin_devices.push_back(std::make_pair(DEFAULT_RSTVEC, &boot_rom));

  // Create spike instance
  preloaded_sim_t sim(&cfg, false, mems, plugin_devices, htif_args, dm_config,
                      dump_ptr, false, nullptr, false, nullptr, SIZE_MAX);

  sim.set_debug(false);
  sim.configure_log(true, false);

  int exit_code = sim.run();

  // Return code of 1 is required by systemverilog (happens if uvm_sw_ipc is
  // used to end simulation)
  // See section 35.9 'Disabling DPI tasks and functions' in the 1800-2017 LRM
  if (svIsDisabledState())
    return 1;

  return exit_code;
};
