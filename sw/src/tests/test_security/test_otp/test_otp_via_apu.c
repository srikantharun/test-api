//---------------------------
// Description
//  Test to verify the accesses to OTP via APU:
//      1 - OTP secure is not accessible via APU
//      2 - OTP public reserved is possible to read via APU. No writes are allowed
//      3 - OTP public unprotected is possible to read and write via APU

#include <memorymap.h>
#include <printf.h>
#include <testutils.h>
#include "../test_security_utils.h"
#include <kse/kse_utils.h>

void test_otp_memory(uint32_t addr_base, uint32_t mem_size, uint32_t allow_wr, uint32_t allow_rd, char *tag_name) {
  uint32_t  addr;
  uint32_t  i;
  uint32_t  ro_expetected_data=0;
  //verify the base address with increments of power of two
  for (addr=addr_base, i=4; addr<addr_base+mem_size; addr=addr_base+i, i=(i<<1)) {
    test_addr_32b(addr, allow_wr, allow_rd, tag_name, ro_expetected_data);
  }
  //verify the last possible (aligned) address
  test_addr_32b(addr_base+mem_size-4, allow_wr, allow_rd, tag_name, ro_expetected_data);
}

int main() {
  //declaration of variables
  uint32_t  addr_base;
  uint32_t  mem_size;
  uint32_t  allow_rd;
  uint32_t  allow_wr;
  char      *tag_name="";

  testcase_init();

  // ----------------------------------------
  // 1 - OTP secure is not accessible via APU
  // OTP secure address range [OTP_MEM_BASE_ADDR : OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE-1]
  //-----------------------------------------
  //run write and read test
  LOG_INF("[OTP Secure] Starting test");
  //set input parameter
  addr_base = OTP_MEM_BASE_ADDR;
  mem_size=OTP_SECURE_SIZE;
  allow_wr=0;
  allow_rd=0;
  tag_name="OTP Secure";
  test_otp_memory(addr_base, mem_size, allow_wr, allow_rd, tag_name);

  //-----------------------------------------
  // 2 - OTP public reserved is possible to read via APU. No writes are allowed
  // OTP public reserved address range [OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE : OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE+OTP_PUBLIC_RESERVED_SIZE-1]
  //-----------------------------------------
  //run write and read test
  LOG_INF("[OTP Public reserved] Starting test");
  //set input parameter
  addr_base = OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE;
  mem_size=OTP_PUBLIC_RESERVED_SIZE;
  allow_wr=0;
  allow_rd=1;
  tag_name="OTP Public reserved";
  test_otp_memory(addr_base, mem_size, allow_wr, allow_rd, tag_name);

  //-----------------------------------------
  // 3 - OTP public unprotected is possible to read and write via APU
  // OTP public unprotected address range [OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE+OTP_PUBLIC_RESERVED_SIZE : OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE+OTP_PUBLIC_RESERVED_SIZE+OTP_PUBLIC_UNPROTECTED_SIZE-1]
  //-----------------------------------------
  //run write and read test
  LOG_INF("[OTP Public unprotected] Starting test");
  //set input parameter
  addr_base = OTP_MEM_BASE_ADDR+OTP_SECURE_SIZE+OTP_PUBLIC_RESERVED_SIZE;
  mem_size=OTP_PUBLIC_UNPROTECTED_SIZE;
  allow_wr=1;
  allow_rd=1;
  tag_name="OTP Public unprotected";
  test_otp_memory(addr_base, mem_size, allow_wr, allow_rd, tag_name);

  //verify that the number of times that entered in IRQ is the same as expected
  CHECK_TRUE((real_cnt==expected_cnt), "Mismatch on the number of times that entered into interrupt");
  return testcase_finalize();
}
