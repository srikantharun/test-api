// LP DMA tests
//
//Test to check lp dma access from l2 to aicore spm
//
//1.Initialise l2 with non zero values
//2.Generate a event and move to uvm test where DMA transfer configs are done.
//3.after that come back to the c test and compare the data

#include <stdbool.h>
#include <testutils.h>
#include <memorymap.h>
#include <memutils.h>
#include <uvm_ipc/uvm_sw_ipc.h>
#include <trap.h>

#define VERBOSE_TESTUTILS

int main() {
  uint64_t seed = 0xa6009b56f74513df;
  uintptr_t *forbidden_addresses = NULL;

  testcase_init();

  mem_write_u64_power_of_2_addresses("L2", L2_MODULE_0_BASE, L2_MODULE_0_SIZE, seed, forbidden_addresses);

  printf("Generating event 16 : Moving to uvm code where the DMA transfers from l2 to spm are executed\n");
  uvm_sw_ipc_gen_event(16);

  uvm_sw_ipc_wait_event(1);
  printf("Waiting for the event 1 from uvm, DMA transfers done, data comparison starting below\n");


  ASSERT(uvm_sw_ipc_memcmp((void *)0x14022000,(void *)L2_MODULE_0_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14022500,(void *)L2_MODULE_1_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14023000,(void *)L2_MODULE_2_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14023500,(void *)L2_MODULE_3_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14024000,(void *)L2_MODULE_4_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14024500,(void *)L2_MODULE_5_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14025000,(void *)L2_MODULE_6_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14025500,(void *)L2_MODULE_7_BASE, 64) == 0);

  return 0;
}
