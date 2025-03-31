#include "uvm_sw_ipc.h"
#include <testutils.h>

void udelay(uint64_t usec) {
  ASSERT(usec <= UINT32_MAX, "udelay is too high!");
  uvm_sw_ipc_udelay(usec);
}
