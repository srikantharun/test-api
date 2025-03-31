// test_l1_preload
// - Create a buffer that fills the l1.
// - The value of each element is its expected address
// - Access the first element of each minibank
// - Verify it has the expected address
//
// test_l1_uvm_sw_ipc_cpy_cmp
// - Once the L1 has been fully preloaded:
//   - Compare its lower half with its upper half. Result should be < 0.
//   - Copy its lower half into its upper half.
//   - Compare both halves again. Result should be < 0.
//   - Set the last 64-bit word of the lower half to UINT64_MAX.
//   - Compare both halves. Result should be > 0.

#include <memorymap.h>
#include <stdint.h>
#include <test_aicore_l1_access/aicore/test_l1_common.h>
#include <testutils.h>
#include <util.h>
#include <uvm_ipc/uvm_sw_ipc.h>

#define L1_BUFFER_SIZE (AICORE_0_L1_SIZE / 8)

extern uint64_t l1_buffer[L1_BUFFER_SIZE] __attribute__((section(".l1")));

void test_l1_preload(void) {
  for (uint64_t i = 0; i < NB_L1_MINIBANKS; i++) {
    for (uint64_t j = 0; j < NB_L1_SUBBANKS; j++) {
      uint64_t expected_address = (uint64_t)get_addr(j, i, 0);
      uintptr_t l1_base_address = AICORE_0_L1_BASE + AICORE_0_SIZE * (r_mhartid()-AI_CORE_0);
      uint64_t array_offset = (expected_address - l1_base_address) / 8;
      CHECK_EQUAL_HEX(expected_address, l1_buffer[array_offset]);
      CHECK_EQUAL_HEX(expected_address + 0x8, l1_buffer[array_offset +1]);
    }
  }
}

 #ifdef UVM_SW_IPC
 void test_l1_uvm_sw_ipc_cpy_cmp(void) {
   uintptr_t l1_base_address = AICORE_0_L1_BASE + AICORE_0_SIZE * (r_mhartid()-AI_CORE_0);
   uint64_t l1_half_size = AICORE_0_L1_SIZE / 2;
   uintptr_t l1_high = l1_base_address + l1_half_size;

   printf("Comparing the lower half of L1 with its upper half\n");
   ASSERT(uvm_sw_ipc_memcmp((void *)l1_base_address, (void *)l1_high,
                                  l1_half_size) < 0);
   printf("Copying the lower half of L1 into its upper half\n");
   uvm_sw_ipc_memcpy((void *)l1_high, (void *)l1_base_address, l1_half_size);
   ASSERT(uvm_sw_ipc_memcmp((void *)l1_base_address, (void *)l1_high,
                                  l1_half_size) == 0);
   printf("Setting the last 64-bit word of L1's lower half to UINT64_MAX\n");
   *(uint64_t *)(l1_high - 8) = UINT64_MAX;

   ASSERT(uvm_sw_ipc_memcmp((void *)l1_base_address, (void *)l1_high,
                                  l1_half_size) > 0);
 }
 #endif

int main() {
  testcase_init();
  test_l1_preload();
   #ifdef UVM_SW_IPC
    test_l1_uvm_sw_ipc_cpy_cmp();
   #endif
  return testcase_finalize();
}
