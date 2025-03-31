#include "dpi_devices.h"
#include <common/include/memorymap.h>
#include <filesystem>
#include <sim.h>

// sim_t override that indicates whether an address block is preloaded
// This allows to use a physical, backdoor-loaded memory.
class preloaded_sim_t : public sim_t {
public:
  preloaded_sim_t(
      const cfg_t *cfg, bool halted,
      std::vector<std::pair<reg_t, mem_t *>> mems,
      std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices,
      const std::vector<std::string> &args,
      const debug_module_config_t &dm_config, const char *log_path,
      bool dtb_enabled, const char *dtb_file, bool socket_enabled,
      FILE *cmd_file, size_t max_steps)
      : sim_t(cfg, halted, mems, plugin_devices, args, dm_config, log_path,
              dtb_enabled, dtb_file, socket_enabled, cmd_file, max_steps) {}
  ~preloaded_sim_t() {};

  // Binary is preloaded by systemverilog
  bool is_address_preloaded(addr_t addr, size_t size) {
    return ((addr >= SYS_SPM_BASE) &&
            ((addr + size) < (SYS_SPM_BASE + SYS_SPM_SIZE)));
  }
};

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

extern "C" int spike_main(const char *elf) {
  std::pair<reg_t, reg_t> initrd_bounds = std::make_pair((reg_t)0, (reg_t)0);
  char *bootargs = nullptr;
  char const *isa = "rv64gcv";
  char const *priv = DEFAULT_PRIV;
  char const *varch = DEFAULT_VARCH;
  bool misaligned = false;
  endianness_t endianness = endianness_little;
  reg_t pmpregions = 16;
  reg_t pmpgranularity = (1 << PMP_SHIFT);
  std::vector<mem_cfg_t>
      mem_layout; // No layout needed, SPM is added independently
  std::vector<size_t> hartids = {0};
  bool real_time_clint = false;
  bool trigger_count = 4;
  std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices;
  cfg_t cfg(initrd_bounds, bootargs, isa, priv, varch, misaligned, endianness,
            pmpregions, mem_layout, hartids, real_time_clint, trigger_count);

  std::vector<std::string> htif_args{elf};
  debug_module_config_t dm_config;
  std::vector<std::pair<reg_t, mem_t *>> mems;
  mems.push_back(
      std::make_pair(AICORE_0_SPM_BASE,
                     new mem_t(AICORE_0_SPM_SIZE))); // Create a fake AICORE_SPM
                                                     // to put the aicore code

#ifdef DUMP_INST
  std::filesystem::path dump_path(elf);
  dump_path = dump_path.replace_filename("instruction_dump_ax65_id0.log");
  const char *dump_ptr = dump_path.c_str();
#else
  char *dump_ptr = nullptr;
#endif

  rom_device_t boot_rom(create_rom());

  // Create DPI devices
  rot_kse_device_t    rot_kse_dpi;
  spm_mem_t spm_dpi;

  // Add all devices
  plugin_devices.push_back(std::make_pair(DEFAULT_RSTVEC, &boot_rom));
  plugin_devices.push_back(std::make_pair(SOC_MGMT_ROT_KSE_BASE, &rot_kse_dpi));
  plugin_devices.push_back(std::make_pair(SYS_SPM_BASE, &spm_dpi));

  // Create spike instance and run it
  auto sim = std::make_unique<preloaded_sim_t>(
      &cfg, false, mems, plugin_devices, htif_args, dm_config, dump_ptr, false,
      nullptr, false, nullptr, SIZE_MAX);

  sim->set_debug(false);
  sim->configure_log(true, false);

  sim->run();

  // Return code of 1 is required by systemverilog.
  // See section 35.9 'Disabling DPI tasks and functions' in the 1800-2017 LRM
  if (svIsDisabledState())
    return 1;

  return 0;
}
