#include <common/include/memorymap.h>
#include <dpi_device.h>
#include <preloaded_sim.h>
#include <sim.h>
#include <sv_tasks.h>
#include <svdpi.h>

#define I2C_MASTER_SIZE 0x8
#define I2C0_MASTER_BASE 0xC0000000 // Fake address to access I2C0 master
#define I2C1_MASTER_BASE 0xC1000000 // Fake address to access I2C0 master

// Declaration of exported UVM tasks
SV_TASK_DECL(soc_periph)
SV_TASK_DECL(spm)
SV_TASK_DECL(i2c0_master)
SV_TASK_DECL(i2c1_master)

extern "C" int spike_main(const char *elf) {

  std::vector<std::pair<reg_t, mem_t *>> mems;
  mems.push_back(
      std::make_pair(AICORE_0_SPM_BASE,
                     new mem_t(AICORE_0_SPM_SIZE))); // Create a fake AICORE_SPM
                                                     // to put the aicore code
  std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices;

  // Create DPI devices
  dpi_device_t soc_periph_dpi(SOC_PERIPH_BASE, 8, SOC_PERIPH_SIZE, false,
                              soc_periph_read, soc_periph_write);
  dpi_device_t spm_dpi(SYS_SPM_BASE, 8, SYS_SPM_SIZE, true, spm_read,
                       spm_write);
  dpi_device_t i2c0_master(I2C0_MASTER_BASE, 1, I2C_MASTER_SIZE, false,
                           i2c0_master_read, i2c0_master_write);
  dpi_device_t i2c1_master(I2C1_MASTER_BASE, 1, I2C_MASTER_SIZE, false,
                           i2c1_master_read, i2c1_master_write);

  // Add all devices
  plugin_devices.push_back(
      std::make_pair(soc_periph_dpi.base_addr(), &soc_periph_dpi));
  plugin_devices.push_back(std::make_pair(spm_dpi.base_addr(), &spm_dpi));
  plugin_devices.push_back(
      std::make_pair(i2c0_master.base_addr(), &i2c0_master));
  plugin_devices.push_back(
      std::make_pair(i2c1_master.base_addr(), &i2c1_master));

  // Create spike instance and run it
  return run_sim(elf, mems, plugin_devices);
}
