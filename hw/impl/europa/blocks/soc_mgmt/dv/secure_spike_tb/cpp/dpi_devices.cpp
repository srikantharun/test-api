#include "dpi_devices.h"
#include "svdpi.h"
#include <common/include/memorymap.h>
#include <iomanip>
#include <iostream>
#include <sim.h>
#include <sstream>

// Print uint8_t numbers into hex format
static char *getHexArrayString(const uint8_t *array, size_t size) {
  std::ostringstream ss;
  ss << std::hex << std::setfill('0');

  for (size_t i = 0; i < size; ++i)
    ss << std::setw(2) << static_cast<int>(array[size - 1 - i]);

  std::string result = ss.str();
  char *cString = new char[result.length() + 1];
  std::strcpy(cString, result.c_str());

  return cString;
}

// Check whether calling exported tasks is allowed
// See section 35.9 'Disabling DPI tasks and functions' in the 1800-2017 LRM
static bool check_ctx_disabled() {
  if (svIsDisabledState()) {
    svAckDisabledState();
    return true;
  }
  return false;
}

// Helper function to debug transactions
static void print_access_info(char *id, reg_t addr, size_t len, uint8_t *bytes,
                              char resp) {
  char *hex_data = getHexArrayString(bytes, len);
  printf("[%s] addr=0x%x, resp=%d, data=0x%s\n", addr, resp, hex_data);
  delete (hex_data);
}

//------------------------------------------------------------------------------
// ROT KSE functions
//------------------------------------------------------------------------------

bool rot_kse_device_t::load(reg_t addr, size_t len, uint8_t *bytes) {
  char resp;
  int max_len;
  svBitVecVal data;
  // Full address is required by ROT KSE
  reg_t full_addr = addr + SOC_MGMT_ROT_KSE_BASE;

  // limit access to 64 bits
  assert(len <= 8);

  if (check_ctx_disabled())
    return false;

  // Call rot_kse_read task defined in uvm/test/spike_top_test.sv
  rot_kse_read(reinterpret_cast<const svBitVecVal *>(&full_addr),
               reinterpret_cast<svBitVecVal *>(bytes), len, &resp);

#ifdef DEBUG
  print_access_info("rot_kse_read", addr, len, bytes, resp);
#endif
  return (RESP_OK == resp);
}
bool rot_kse_device_t::store(reg_t addr, size_t len, const uint8_t *bytes) {
  char resp;
  // Full address is required by ROT KSE
  reg_t full_addr = addr + SOC_MGMT_ROT_KSE_BASE;

  // limit access to 64 bits
  assert(len <= 8);

  if (check_ctx_disabled())
    return false;

  // Call rot_kse_write task defined in uvm/test/spike_top_test.sv
  rot_kse_write(reinterpret_cast<const svBitVecVal *>(&full_addr),
                reinterpret_cast<const svBitVecVal *>(bytes), len, &resp);

#ifdef DEBUG
  print_access_info("rot_kse_write", addr, len, bytes, resp);
#endif

  return (RESP_OK == resp);
}

//------------------------------------------------------------------------------
// SPM functions
//------------------------------------------------------------------------------

bool spm_mem_t::load(reg_t addr, size_t len, uint8_t *bytes) {
  char resp;
  int max_len;
  svBitVecVal data;
  reg_t full_addr = addr + SYS_SPM_BASE;

  // limit access to 64 bits
  assert(len <= 8);

  if (check_ctx_disabled()) {
    // Disabled context == end of simulation
    // We return 1 to signify the FESVR to exit
    if (addr == TOHOST_OFFSET) {
      *reinterpret_cast<uint64_t *>(bytes) = 1u;
      return true;
    }
    return false;
  }

  spm_read(reinterpret_cast<const svBitVecVal *>(&full_addr),
           reinterpret_cast<svBitVecVal *>(bytes), len, &resp);

#ifdef DEBUG
  print_access_info("spm_read", addr, len, bytes, resp);
#endif

  return (RESP_OK == resp);
}

bool spm_mem_t::store(reg_t addr, size_t len, const uint8_t *bytes) {
  char resp;
  reg_t full_addr = addr + SYS_SPM_BASE;

  // limit access to 64 bits
  assert(len <= 8);

  if (check_ctx_disabled()) {
    // We want to always return true for accesses to tohost
    // otherwise the spike crashes (and the simulator with it)
    if (addr == TOHOST_OFFSET) {
      return true;
    }
    return false;
  }

  spm_write(reinterpret_cast<const svBitVecVal *>(&full_addr),
            reinterpret_cast<const svBitVecVal *>(bytes), len, &resp);

#ifdef DEBUG
  print_access_info("spm_write", addr, len, bytes, resp);
#endif

  return (RESP_OK == resp);
}
