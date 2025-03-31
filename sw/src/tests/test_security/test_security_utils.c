#include <memorymap.h>
#include <regutils.h>
#include <printf.h>
#include <testutils.h>
#include <timer.h>
#include "test_security_utils.h"
#include <rng.h>

uint64_t kse_seed = 0xcafedecadeadbeef;

// override default handler so we can handle bus errors gracefully
void local_irq_bwe_handler(void) {

    if (expect_bwe_irq) {
        real_cnt++;
    } else {
        LOG_ERR("Unexpected bus transaction error received\n");
        abort();
    }
}

//---------- common functions -------------------
void update_irq_aux_var(uint32_t allow_access)
{
  if(!allow_access) {
    //allow irq to happen
    expect_bwe_irq=true;
    expected_cnt++;
  }
  else {
    expect_bwe_irq=false;
  }
}

void test_addr_32b(uint32_t addr, uint32_t allow_wr, uint32_t allow_rd, char *tag_name, uint32_t ro_expected_data) {
  uint32_t  data_read;
  uint32_t  data2write;
  uint32_t  expected_data;
  data2write = (uint32_t)(xorshift64(&kse_seed));
  LOG_DBG("[%s] Accessing address 0x%0x", tag_name, addr);
  update_irq_aux_var(allow_wr);
  set_reg_u32((uintptr_t) addr, data2write);
  udelay(1); //make sure the interrupt happens

  update_irq_aux_var(allow_rd);
  data_read = get_reg_u32((uintptr_t) addr);
  udelay(1); //make sure the interrupt happens

  //set expetected data to 0
  if(     (!allow_wr) && (!allow_rd)) expected_data = 0;
  else if((!allow_wr) && ( allow_rd)) expected_data = ro_expected_data;
  else                                expected_data = data2write;

  CHECK_EQUAL_HEX(expected_data,data_read, "Mismatch on address access");
}
