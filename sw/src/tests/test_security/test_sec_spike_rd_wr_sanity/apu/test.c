#include <printf.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <memorymap.h>
#include <test_security/test_integration/include/secure_ip_hal.h>
#include <test_security/test_integration/include/secure_ip.h>

#define store(_type, _offset)                                                  \
  *(volatile _type *)(device_addr + _offset) = (_type)init_val
#define load(_type, _offset)                                                   \
  (uint64_t)(*(volatile _type *)(device_addr + _offset))

int main() {
  uintptr_t device_addr = SOC_MGMT_ROT_KSE_BASE;
  uint64_t init_val = 0xCAFEBABEDEADBEEFu;

  testcase_init();

  store(uint64_t, 0);
  store(uint32_t, 4);
  store(uint32_t, 0);
  store(uint16_t, 2);
  store(uint8_t, 5);

  CHECK_EQUAL_HEX(load(uint64_t, 0), 0xDEADEFEFBEEFBEEFu);
  CHECK_EQUAL_HEX(load(uint32_t, 0), 0xBEEFBEEFu);
  CHECK_EQUAL_HEX(load(uint32_t, 4), 0xDEADEFEFu);
  CHECK_EQUAL_HEX(load(uint16_t, 4), 0xEFEFu);
  CHECK_EQUAL_HEX(load(uint8_t, 6), 0xADu);

  return testcase_finalize();
}
