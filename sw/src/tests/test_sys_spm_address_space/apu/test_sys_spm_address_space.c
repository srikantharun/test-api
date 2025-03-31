// check that the SYS-SPM memory has a defined size of 8MiB by writing/reading
// in its powers of 2

#include <stdbool.h>
#include <testutils.h>
#include <memorymap.h>
#include <memutils.h>


int main() {
  uint64_t seed = 0xc6cc2ce096ec1744;
  uint64_t sys_spm_8mb_size = 8*1024*1024; // hardcoded on purpose, in case memorymap is less than 8MB
#ifdef SYSTEM_TOP
  uintptr_t forbidden_addresses[] = {
    SYS_SPM_BASE + 0x2000, // uvm_sw_ipc region
    SYS_SPM_BASE + 0x4000, // code is here
    SYS_SPM_BASE + 0x8000, // code is here
    0, // end of array
  };
#else
  uintptr_t *forbidden_addresses = NULL;
#endif

  testcase_init();

  mem_write_u64_power_of_2_addresses("SYS_SPM", SYS_SPM_BASE, sys_spm_8mb_size, seed, forbidden_addresses);
  mem_check_read_u64_power_of_2_addresses("SYS_SPM", SYS_SPM_BASE, sys_spm_8mb_size, seed, forbidden_addresses);

  return testcase_finalize();
}
