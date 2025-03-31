#include <stddef.h>
#include <cache.h>
#include "../test_uvm_sw_ipc_common.h"

int main() {
  int ret;
  dcache_disable();
  ret = test_uvm_sw_ipc_mem(NULL);
  dcache_enable();
  return ret;
}
