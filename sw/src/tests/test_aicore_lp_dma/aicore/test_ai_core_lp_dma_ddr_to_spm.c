// LP DMA tests
//
//Test to check lp dma access from ddr to aicore spm
//
//1.Initialise DDRs with non zero values
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

  mem_write_u64_power_of_2_addresses("DDR_0", DDR_0_BASE, 128, seed, forbidden_addresses);
  mem_write_u64_power_of_2_addresses("DDR_1", DDR_1_BASE, 128, seed, forbidden_addresses);

  printf("Generating event 16 : Moving to uvm code where the DMA transfers from ddr to aicore spm are executed\n");
  uvm_sw_ipc_gen_event(16);

  uvm_sw_ipc_wait_event(1);
  printf("Waiting for the event 1 from uvm, DMA transfers done, data comparison starting below\n");

  ASSERT(uvm_sw_ipc_memcmp((void *)0x14030000,(void *)DDR_0_BASE, 64) == 0);
  ASSERT(uvm_sw_ipc_memcmp((void *)0x14031000,(void *)DDR_1_BASE, 64) == 0);

  return 0;
}
