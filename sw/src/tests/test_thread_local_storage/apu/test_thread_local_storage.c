#include <asm.h>
#include <multicore.h>
#include <testutils.h>
#include <thread.h>
#include <util.h>

#include "../test_thread_local_storage_common.h"

int main(void) {
  int ret = 0;
  
  // APU
  for (size_t i = 0; i < HW_DEFINES_APU_CORE_NUMBER; i++) {
    printf("test_thread_local_storage (APU core %0d)...\n", i);
    if (i == 0) {
      ret |= test_thread_local_storage(NULL);
    } else {
      thread_launch(i, test_thread_local_storage, NULL);
      ret |= thread_join(i);
    }
  }

  // TODO: AICORE 0-7
  
  // PVE0
  printf("test_thread_local_storage (PVE 0)...\n");
  start_cores_pve0();
  ret |= wait_cores_pve0();

  // TODO: PVE1

  return ret;
}
