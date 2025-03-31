#include <memorymap.h>
#include <printf.h>
#include <string.h>
#include <uvm_ipc/uvm_sw_ipc.h>
#include <testutils.h>

__attribute__((aligned(8))) char golden[16] = {
  0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
  0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff
};
__attribute__((aligned(8))) char scratch[16];

// `other_memory_buf` shall point to a 16-byte buffer in the other memory and
// shall be 8-byte aligned.
void check_uvm_backdoor_to_memory(const char *other_memory_name, char *other_memory_buf) {
  printf("testing %s @ 0x%010lx\n", other_memory_name, other_memory_buf);
  printf("testing UVM backdoor WRITE to %s...\n", other_memory_name);
  // Copy data to other memory via UVM backdoor
  uvm_sw_ipc_memcpy(other_memory_buf, golden, sizeof(golden));
  // Check the data is correct via frontdoor
  CHECK_TRUE(memcmp(other_memory_buf, golden, sizeof(golden)) == 0, "uvm_sw_ipc_memcpy failed (write to other memory failed)");

  printf("testing UVM backdoor READ from %s...\n", other_memory_name);
  // Copy data back to scratch buffer via UVM backdoor
  uvm_sw_ipc_memcpy(scratch, other_memory_buf, sizeof(golden));
  // Check the data is correct (via UVM backdoor as it is faster)
  CHECK_TRUE(uvm_sw_ipc_memcmp(scratch, golden, sizeof(golden)) == 0, "uvm_sw_ipc_memcpy failed (read from other memory failed)");
}


int main(void) {
  printf("*** starting test_uvm_sw_ipc_all_memories...\n");
  testcase_init();

  check_uvm_backdoor_to_memory("fake DDR", (char*)DDR_1_BASE);

  return testcase_finalize();
}
