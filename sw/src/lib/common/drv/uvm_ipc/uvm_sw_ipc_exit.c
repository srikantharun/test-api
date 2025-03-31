#include "uvm_sw_ipc.h"

void __attribute__((noreturn)) exit(int code)
{
  if (code == 0) {
    uvm_sw_ipc_print_info(0, "FW simulation PASS");
  } else {
    uvm_sw_ipc_print_error(1, "FW simulation FAIL (exit code=%0d)", code);
  }
  uvm_sw_ipc_quit(); // finishes simulation, prints UVM report

  while (1) {
    asm("wfi");
  }
}
