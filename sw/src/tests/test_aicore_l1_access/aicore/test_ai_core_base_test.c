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

  testcase_init();

  printf("Generating event 16 : Moving to uvm code where the respective uvm code will execute. It will be written in uvm code description.\n");
  uvm_sw_ipc_gen_event(16);

  uvm_sw_ipc_wait_event(1);
  printf("Waiting for the event 1 from uvm\n");

  return 0;
}
