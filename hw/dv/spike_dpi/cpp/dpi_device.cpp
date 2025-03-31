#include "dpi_device.h"
#include "svdpi.h"
#include <cstring>
#include <iomanip>
#include <iostream>
#include <sim.h>
#include <sstream>
#include <string>

using namespace std;

// Print uint8_t numbers into hex format
static char *getHexArrayString(const uint8_t *array, size_t size) {
  std::ostringstream ss;
  ss << hex << setfill('0');

  for (size_t i = 0; i < size; ++i)
    ss << setw(2) << static_cast<int>(array[size - 1 - i]);

  string result = ss.str();
  char *cString = new char[result.length() + 1];
  strcpy(cString, result.c_str());

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
// SOC PERIPH functions
//------------------------------------------------------------------------------

bool dpi_device_t::load(reg_t addr, size_t len, uint8_t *bytes) {
  char resp;
  int max_len;
  svBitVecVal data;
  reg_t full_addr = addr + _base_addr;

  assert(len <= max_access_len);

if (check_ctx_disabled()) {
    // Disabled context == end of simulation
    // We return 1 to signify the FESVR to exit
    if (full_addr == TOHOST_ADDR) {
      *reinterpret_cast<uint64_t *>(bytes) = 1u;
      return true;
    }
    return false;
  }

  // Call soc_periph_read task defined in uvm/test/spike_top_test.sv
  read_func(reinterpret_cast<const svBitVecVal *>(&full_addr),
            reinterpret_cast<svBitVecVal *>(bytes), len, &resp);

#ifdef DEBUG
  print_access_info("load", addr, len, bytes, resp);
#endif
  return (RESP_OK == resp);
}

bool dpi_device_t::store(reg_t addr, size_t len, const uint8_t *bytes) {
  char resp;
  reg_t full_addr = addr + _base_addr;

  assert(len <= max_access_len);

if (check_ctx_disabled()) {
    // We want to always return true for accesses to tohost
    // otherwise the spike crashes (and the simulator with it)
    if (full_addr == TOHOST_ADDR) {
      return true;
    }
    return false;
  }

  write_func(reinterpret_cast<const svBitVecVal *>(&full_addr),
             reinterpret_cast<const svBitVecVal *>(bytes), len, &resp);

#ifdef DEBUG
  print_access_info("store", addr, len, bytes, resp);
#endif

  return (RESP_OK == resp);
}
