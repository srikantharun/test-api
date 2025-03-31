#include <common/include/memorymap.h>
#include <dpi_device.h>
#include <preloaded_sim.h>
#include <sim.h>
#include <sv_tasks.h>
#include <svdpi.h>

// Declaration of exported UVM tasks
// ====== TODO: Add your own tasks here ======
// SV_TASK_DECL(my_periph)
// ===========================================

extern "C" int spike_main(const char *elf, int *exit_code) {

  // Add any memory here that is required to play the elf but does not have
  // to access it physically
  std::vector<std::pair<reg_t, mem_t *>> mems;
  // ======================= TODO =======================
  // Example: Here we create a fake AICORE_SPM to put the aicore code
  // mems.push_back(
  //     std::make_pair(AICORE_0_SPM_BASE,
  //                    new mem_t(AICORE_0_SPM_SIZE)));
  // ====================================================

  std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices;

  // ====== TODO: Create DPI devices, one per IP you need to access ======
  // dpi_device_t my_periph_dpi(MY_PERIPH_ADDR, 8, MY_PERIPH_SIZE, false,
  //                        my_periph_read, my_periph_write);
  // =====================================================================

  // ====== TODO: Add created devices to the plugin_devices ======
  // plugin_devices.push_back(
  //     std::make_pair(my_periph_dpi.base_addr(), &my_periph_dpi));
  // =============================================================

  // Create spike instance and run it
  *exit_code = run_sim(elf, mems, plugin_devices);
  return *exit_code;
}
