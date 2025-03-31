#pragma once

#include <dpi_device.h>
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
              dtb_enabled, dtb_file, socket_enabled, cmd_file, max_steps),
        device_list() {
    for (auto &device_pair : plugin_devices) {
      device_list.push_back(
          reinterpret_cast<dpi_device_t *>(device_pair.second));
    }
  }

  bool is_address_preloaded(addr_t addr, size_t size);

private:
  std::vector<dpi_device_t *> device_list;
};

int run_sim(std::string elf, std::vector<std::pair<reg_t, mem_t *>> mems,
            std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices);
