#ifndef DPI_DEVICES_H
#define DPI_DEVICES_H

#include "svdpi.h"
#include <common/include/memorymap.h>
#include <sim.h>

#define RESP_OK 0
#define TOHOST_OFFSET 0x1000 // tohost offset inside SYS_SPM
#define I2C_MASTER_SIZE 0x8
#define I2C0_MASTER_BASE 0xC0000000 // Fake address to access I2C0 master
#define I2C1_MASTER_BASE 0xC1000000 // Fake address to access I2C0 master

//------------------------------------------------------------------------------
// UVM TASKS DECLARATION
//------------------------------------------------------------------------------

// Tasks are defined in ../uvm/test/spike_dpi_export.sv
extern "C" int soc_periph_read(const svBitVecVal *addr, svBitVecVal *data,
                               int len, char *resp);

extern "C" int soc_periph_write(const svBitVecVal *addr,
                                const svBitVecVal *data, int len, char *resp);

extern "C" int spm_read(const svBitVecVal *addr, svBitVecVal *data, int len,
                        char *resp);

extern "C" int spm_write(const svBitVecVal *addr, const svBitVecVal *data,
                         int len, char *resp);

extern "C" int i2c0_master_read(const svBitVecVal *addr, svBitVecVal *data,
                                int len, char *resp);

extern "C" int i2c0_master_write(const svBitVecVal *addr,
                                 const svBitVecVal *data, int len, char *resp);

extern "C" int i2c1_master_read(const svBitVecVal *addr, svBitVecVal *data,
                                int len, char *resp);

extern "C" int i2c1_master_write(const svBitVecVal *addr,
                                 const svBitVecVal *data, int len, char *resp);

//------------------------------------------------------------------------------
// SPIKE devices
//------------------------------------------------------------------------------

class soc_periph_device_t : public abstract_device_t {
public:
  bool load(reg_t addr, size_t len, uint8_t *bytes);
  bool store(reg_t addr, size_t len, const uint8_t *bytes);
  size_t size() { return SOC_PERIPH_SIZE; }
};

class spm_mem_t : public abstract_device_t {
public:
  bool load(reg_t addr, size_t len, uint8_t *bytes);
  bool store(reg_t addr, size_t len, const uint8_t *bytes);
  size_t size() { return SYS_SPM_SIZE; }
};

class i2c_master_device_t : public abstract_device_t {
public:
  i2c_master_device_t(reg_t base_addr) : base_addr(base_addr) {}
  bool load(reg_t addr, size_t len, uint8_t *bytes);
  bool store(reg_t addr, size_t len, const uint8_t *bytes);
  size_t size() { return I2C_MASTER_SIZE; }

private:
  reg_t base_addr;
};

#endif // DPI_DEVICES_H
