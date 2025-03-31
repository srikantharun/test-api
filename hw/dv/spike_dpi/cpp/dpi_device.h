#pragma once

#include "svdpi.h"
#include <sim.h>
#include <common/include/memorymap.h>

#define RESP_OK 0
#define TOHOST_ADDR (SYS_SPM_BASE+0x1000) //tohost address for fesvr communication

//------------------------------------------------------------------------------
// SPIKE devices
//------------------------------------------------------------------------------

typedef int (*load_dpi_func)(const svBitVecVal *addr, svBitVecVal *data,
                             int len, char *resp);

typedef int (*store_dpi_func)(const svBitVecVal *addr, const svBitVecVal *data,
                              int len, char *resp);

class dpi_device_t : public abstract_device_t {
public:
  dpi_device_t(reg_t base_addr, size_t max_access_len, size_t size, bool preloaded,
               load_dpi_func read_func, store_dpi_func write_func)
      : _base_addr(base_addr), max_access_len(max_access_len), _size(size), preloaded(preloaded),
        read_func(read_func), write_func(write_func) {}
  bool load(reg_t addr, size_t len, uint8_t *bytes);
  bool store(reg_t addr, size_t len, const uint8_t *bytes);
  size_t size() { return _size; }
  reg_t base_addr() { return _base_addr; }
  bool is_preloaded() {return  preloaded;}

private:
  store_dpi_func write_func;
  load_dpi_func read_func;
  reg_t _base_addr;
  size_t max_access_len;
  size_t _size;
  bool preloaded;
};
