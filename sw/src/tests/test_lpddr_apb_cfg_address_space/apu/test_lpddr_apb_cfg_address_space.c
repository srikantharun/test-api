// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Rodrigo Borges <rodrigo.borges@axelera.ai>
//
// Description: This test demonstrates that we reach all the register
//              configuration space of the LPDDR controller.
//              Read the first and last readable configuration address of:
//              REGB_FREQf_CH0 (f from 0 to 3 - there is no CH1)
//              REGB_DDRC_CH0 (no CH1)
//              REGB_ARB_PORTp (p is 0 due to only having 1 AXI port)
//              REGB_ADDR_MAP0
//              For register descriptions check Synopsys Controller IP LPDDR5X/5/4X
//              Memory Controller Reference Manual - Version 1.60a-lca00 (May 2024) - Chapter 3

#include <lpddr/drv_lpddr.h>

int main() {

  uint32_t apb_read_data;
  uint64_t apb_address;

  testcase_init();

  // Disable LPDDR NOC fences for LPDDR subsystem APB interfaces
  lpddrNocFenceTargCfg(LPDDR_MODULE_NUM, LPDDR_NOC_FENCE_DISABLE);

  // Section 14.1.2 Controller Initialization (Controller Databook - Version 1.60a-lca00 - May2024)
  // 4. De-assert presetn once the clocks are active and stable
  lpddrModuleApbReset(LPDDR_MODULE_NUM, LPDDR_RESET_DEASSERT);
  printf("INFO: Released LPDDR ctrl cfg interface reset.\n");

  // 5. Allow 128 APB clock cycles for synchronization of presetn to core_ddrc_core_clk and
  // aclk/chi_clk_pn domains and to permit initialization of end logic
  // APB clock @ 800 MHz (1.25 ns)
  // APU clock @ 1200 MHz(0.833333333 ns)
  // 128 * 1.25 = 160
  // 160/0.833333333 = 192.00000007680000003
  cycledelay(200);

  // 7. De-assert the resets core_ddrc_rstn, ras_log_rstn, sbr_resetn, and aresetn/chi_resetn_pn
  lpddrCtlCoreReset(LPDDR_MODULE_NUM, LPDDR_RESET_DEASSERT);

  // Deassert PHY Reset
  lpddrPhyReset(LPDDR_MODULE_NUM, LPDDR_RESET_DEASSERT);

  // Section 6.2 Resets
  // After the deassertion of both Reset and PRESETn_APB , the PHY must receive at least 64 DfiClk
  // pulses prior to any APB transaction or an assertion of dfi_init_start.
  // DFI clock @ 800 MHz (1.25 ns)
  // APU clock @ 1200 MHz(0.833333333 ns)
  // 64 * 1.25 = 80
  // 80/0.833333333 = 96.000000038400000015
  cycledelay(100);

  // REGB_FREQf_CH0 (f corresponds to freq_num, from 0 to 3)
  for (uint32_t freq_num = 0; freq_num < 4; freq_num++)
  {
    // DRAMSET1TMG0
    apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG0 + (freq_num * 0x100000);
    apb_read_data = get_reg_u32(apb_address);
    printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
    CHECK_EQUAL_HEX(DRAMSET1TMG0_RegisterResetValue, apb_read_data);

    // LNKECCCTL0
    apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_FREQ0_CH0_LNKECCCTL0 + (freq_num * 0x100000);
    apb_read_data = get_reg_u32(apb_address);
    printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
    CHECK_EQUAL_HEX(LNKECCCTL0_RegisterResetValue, apb_read_data);
  }

  // REGB_DDRC_CH0
  // MSTR0
  apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_DDRC_CH0_MSTR0;
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
  CHECK_EQUAL_HEX(MSTR0_RegisterResetValue, apb_read_data);

  // DDRCTL_VER_TYPE
  apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_DDRC_CH0_DDRCTL_VER_TYPE;
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
  CHECK_EQUAL_HEX(DDRCTL_VER_TYPE_RegisterResetValue, apb_read_data);

  // REGB_ARB_PORTp
  // PCCFG
  apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_ARB_PORT0_PCCFG;
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
  CHECK_EQUAL_HEX(PCCFG_RegisterResetValue, apb_read_data);

  // PSTAT
  apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_ARB_PORT0_PSTAT;
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
  CHECK_EQUAL_HEX(PSTAT_RegisterResetValue, apb_read_data);

  // REGB_ADDR_MAP0
  // ADDRMAP1
  apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_ADDR_MAP0_ADDRMAP1;
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n", apb_address, apb_read_data);
  CHECK_EQUAL_HEX(ADDRMAP1_RegisterResetValue, apb_read_data);

  // ADDRMAP12
  apb_address = DDR_0_CTRL_UMCTL2_BASE + LPDDR_REGB_ADDR_MAP0_ADDRMAP12;
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR CTL Address = 0x%x | Value = 0x%x\n" ,apb_address, apb_read_data);
  CHECK_EQUAL_HEX(ADDRMAP12_RegisterResetValue, apb_read_data);

#ifndef PLATFORM_VELOCE

  printf("INFO: Starting APB accesses to LPDDR PHY\n");

  // DFIMRL_p0
  apb_address = DDR_0_CTRL_PHY_PUB_BASE + (DWC_DDRPHYA_DBYTE0_p0_DFIMRL_p0_AddressOffset<<2);
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR PHY Address = 0x%x | Value = 0x%x\n" ,apb_address, apb_read_data);
  CHECK_EQUAL_HEX(DWC_DDRPHYA_DBYTE0_p0_DFIMRL_p0_RegisterResetValue, apb_read_data);

  // PpgcChkMskPat3
  apb_address = DDR_0_CTRL_PHY_PUB_BASE + (DWC_DDRPHYA_DBYTE3_p0_PpgcChkMskPat3_AddressOffset<<2);
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR PHY Address = 0x%x | Value = 0x%x\n" ,apb_address, apb_read_data);
  CHECK_EQUAL_HEX(DWC_DDRPHYA_DBYTE3_p0_PpgcChkMskPat3_RegisterResetValue, apb_read_data);

  // DfiFreqRatio_p0
  apb_address = DDR_0_CTRL_PHY_PUB_BASE + (DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0_AddressOffset<<2);
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR PHY Address = 0x%x | Value = 0x%x\n" ,apb_address, apb_read_data);
  CHECK_EQUAL_HEX(DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0_RegisterResetValue, apb_read_data);

  // PclkGateControl
  apb_address = DDR_0_CTRL_PHY_PUB_BASE + (DWC_DDRPHYA_MASTER0_p0_PclkGateControl_AddressOffset<<2);
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR PHY Address = 0x%x | Value = 0x%x\n" ,apb_address, apb_read_data);
  CHECK_EQUAL_HEX(DWC_DDRPHYA_MASTER0_p0_PclkGateControl_RegisterResetValue, apb_read_data);

  // AcPipeEn_p0
  apb_address = DDR_0_CTRL_PHY_PUB_BASE + (DWC_DDRPHYA_AC0_p0_AcPipeEn_p0_AddressOffset<<2);
  apb_read_data = get_reg_u32(apb_address);
  printf("LPDDR PHY Address = 0x%x | Value = 0x%x\n" ,apb_address, apb_read_data);
  CHECK_EQUAL_HEX(DWC_DDRPHYA_AC0_p0_AcPipeEn_p0_RegisterResetValue, apb_read_data);

#endif // PLATFORM_VELOCE

  return testcase_finalize();
}
