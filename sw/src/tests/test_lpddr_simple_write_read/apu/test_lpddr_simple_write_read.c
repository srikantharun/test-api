#include <lpddr/drv_lpddr.h>
#include <memutils.h>

#define DDR_BASE DDR_0_BASE
#define DDR_SIZE (DDR_0_SIZE / 4)

int main() {
  testcase_init();
  #ifdef REAL_LPDDR
    lpddrSubsystemInit(false);
  #endif

  uint64_t* p_address;
  uint64_t wdata;
  uint64_t rdata;

  p_address = (uint64_t *)(DDR_BASE);
  wdata = 0x1111222233334444;
  *p_address = wdata;
  printf("Write 0x%lx to address 0x%lx\n", wdata, (uint64_t)p_address);

  p_address = (uint64_t *)(DDR_BASE + 0x100 + 0x8);
  wdata = 0x5555666677778888;
  *p_address = wdata;
  printf("Write 0x%lx to address 0x%lx\n", wdata, (uint64_t)p_address);

  p_address = (uint64_t *)(DDR_BASE + 0x1000 + 0x10);
  wdata = 0x9999AAAABBBBCCCC;
  *p_address = wdata;
  printf("Write 0x%lx to address 0x%lx\n", wdata, (uint64_t)p_address);

  p_address = (uint64_t *)(DDR_BASE + 0x10000 + 0x18);
  wdata = 0xDDDDEEEEFFFF0101;
  *p_address = wdata;
  printf("Write 0x%lx to address 0x%lx\n", wdata, (uint64_t)p_address);

  p_address = (uint64_t *)(DDR_BASE);
  rdata = *p_address;
  printf("Read 0x%lx (should have been 0x%lx) from address 0x%lx\n", rdata, 0x1111222233334444, (uint64_t)p_address);
  CHECK_EQUAL_HEX(0x1111222233334444, rdata);

  p_address = (uint64_t *)(DDR_BASE + 0x100 + 0x8);
  rdata = *p_address;
  printf("Read 0x%lx (should have been 0x%lx) from address 0x%lx\n", rdata, 0x5555666677778888, (uint64_t)p_address);
  CHECK_EQUAL_HEX(0x5555666677778888, rdata);

  p_address = (uint64_t *)(DDR_BASE + 0x1000 + 0x10);
  rdata = *p_address;
  printf("Read 0x%lx (should have been 0x%lx) from address 0x%lx\n", rdata, 0x9999AAAABBBBCCCC, (uint64_t)p_address);
  CHECK_EQUAL_HEX(0x9999AAAABBBBCCCC, rdata);

  p_address = (uint64_t *)(DDR_BASE + 0x10000 + 0x18);
  rdata = *p_address;
  printf("Read 0x%lx (should have been 0x%lx) from address 0x%lx\n", rdata, 0xDDDDEEEEFFFF0101, (uint64_t)p_address);
  CHECK_EQUAL_HEX(0xDDDDEEEEFFFF0101, rdata);

  return testcase_finalize();
}
