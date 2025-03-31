//---------------------------
// Description
//  Test to verify the accesses to AOR via APU:
//      - SoC_Config0, SoC_Config0_inv, SoC_Config1, SoC_Config1_inv, Plt_Config and Plt_Config_inv are RO
//      - KSE3_State, KSE3_State_inv and KSE3_FR0/1/2/3/4/5/6/7 are not possible to access

#include <memorymap.h>
#include <regutils.h>
#include <printf.h>
#include <testutils.h>
#include <timer.h>
#include "../test_security_utils.h"
#include <kse/kse_utils.h>


int main() {
  //declaration of variables
  uint32_t  allow_rd;
  uint32_t  allow_wr;
  uint32_t  ro_expetected_data;

  testcase_init();

  kse_execute_after_reset_sequence();

  LOG_INF("Starting test AOR of KSE");

  //Set allow_rd and clear allow_wr
  allow_wr=0;
  allow_rd=1;
  ro_expetected_data=0xFF;
  //test SoC_Config0
  test_addr_32b(KSE_AOR_SOC_CONFIG0_ADDR, allow_wr, allow_rd, "SoC_Config0", ro_expetected_data);
  //test SoC_Config0_inv
  ro_expetected_data=0x0;
  test_addr_32b(KSE_AOR_SOC_CONFIG0_INV_ADDR, allow_wr, allow_rd, "SoC_Config0_inv", ro_expetected_data);
  //test SoC_Config1
  ro_expetected_data=0xFF;
  test_addr_32b(KSE_AOR_SOC_CONFIG1_ADDR, allow_wr, allow_rd, "SoC_Config1", ro_expetected_data);
  //test SoC_Config1_inv
  ro_expetected_data=0x0;
  test_addr_32b(KSE_AOR_SOC_CONFIG1_INV_ADDR, allow_wr, allow_rd, "SoC_Config1_inv", ro_expetected_data);
  //test Plt_Config
  ro_expetected_data=0x0;
  test_addr_32b(KSE_AOR_PLT_CONFIG_ADDR, allow_wr, allow_rd, "Plt_Config", ro_expetected_data);
  //test Plt_Config_inv
  ro_expetected_data=0xFF;
  test_addr_32b(KSE_AOR_PLT_CONFIG_INV_ADDR, allow_wr, allow_rd, "Plt_Config_inv", ro_expetected_data);

  //clear allow_rd and allow_wr
  allow_wr=0;
  allow_rd=0;
  ro_expetected_data=0x0;
  //test KSE3_State
  test_addr_32b(KSE_AOR_KSE3_STATE_ADDR, allow_wr, allow_rd, "KSE3_State", ro_expetected_data);
  //test KSE3_State_inv
  test_addr_32b(KSE_AOR_KSE3_STATE_INV_ADDR, allow_wr, allow_rd, "KSE3_State", ro_expetected_data);
  //test KSE3_FR0
  test_addr_32b(KSE_AOR_KSE3_FR0_ADDR, allow_wr, allow_rd, "KSE3_FR0", ro_expetected_data);
  //test KSE3_FR1
  test_addr_32b(KSE_AOR_KSE3_FR1_ADDR, allow_wr, allow_rd, "KSE3_FR1", ro_expetected_data);
  //test KSE3_FR2
  test_addr_32b(KSE_AOR_KSE3_FR2_ADDR, allow_wr, allow_rd, "KSE3_FR2", ro_expetected_data);
  //test KSE3_FR3
  test_addr_32b(KSE_AOR_KSE3_FR3_ADDR, allow_wr, allow_rd, "KSE3_FR3", ro_expetected_data);
  //test KSE3_FR4
  test_addr_32b(KSE_AOR_KSE3_FR4_ADDR, allow_wr, allow_rd, "KSE3_FR4", ro_expetected_data);
  //test KSE3_FR5
  test_addr_32b(KSE_AOR_KSE3_FR5_ADDR, allow_wr, allow_rd, "KSE3_FR5", ro_expetected_data);
  //test KSE3_FR6
  test_addr_32b(KSE_AOR_KSE3_FR6_ADDR, allow_wr, allow_rd, "KSE3_FR6", ro_expetected_data);
  //test KSE3_FR7
  test_addr_32b(KSE_AOR_KSE3_FR7_ADDR, allow_wr, allow_rd, "KSE3_FR7", ro_expetected_data);

  return testcase_finalize();
}
