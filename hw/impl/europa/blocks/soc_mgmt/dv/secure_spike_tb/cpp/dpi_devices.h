#ifndef DPI_DEVICES_H
#define DPI_DEVICES_H

#include "svdpi.h"
#include <common/include/memorymap.h>
#include <sim.h>

#define RESP_OK 0
#define TOHOST_OFFSET 0x1000 // tohost offset inside SYS_SPM

//------------------------------------------------------------------------------
// UVM TASKS DECLARATION
//------------------------------------------------------------------------------

extern "C" int rot_kse_read(const svBitVecVal *addr, svBitVecVal *data,
                               int len, char *resp);

extern "C" int rot_kse_write(const svBitVecVal *addr,
                                const svBitVecVal *data, int len, char *resp);

extern "C" int spm_read(const svBitVecVal *addr, svBitVecVal *data, int len,
                        char *resp);

extern "C" int spm_write(const svBitVecVal *addr, const svBitVecVal *data,
                         int len, char *resp);

//------------------------------------------------------------------------------
// SPIKE devices
//------------------------------------------------------------------------------

class rot_kse_device_t : public abstract_device_t {
public:
  bool load(reg_t addr, size_t len, uint8_t *bytes);
  bool store(reg_t addr, size_t len, const uint8_t *bytes);
  size_t size() { return SOC_MGMT_ROT_KSE_SIZE; }
};

class spm_mem_t : public abstract_device_t {
public:
  bool load(reg_t addr, size_t len, uint8_t *bytes);
  bool store(reg_t addr, size_t len, const uint8_t *bytes);
  size_t size() { return SYS_SPM_SIZE; }
};

#endif // DPI_DEVICES_H
