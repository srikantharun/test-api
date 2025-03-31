#include "drv_lpddr.h"

/* \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ LPDDR PCTL related methods \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ */

// Auxiliary method to get base address of SYS CFG registers of each LPDDR module
uintptr_t lpddrSysCfgGetRegOffset(unsigned int moduleNum)
{
    ASSERT(moduleNum < 8, "Unsupported model number %d", moduleNum);

    switch(moduleNum) {
        case 7:
            return SYS_CFG_DDR_7_AO_CSR_BASE;
        case 6:
            return SYS_CFG_DDR_6_AO_CSR_BASE;
        case 5:
            return SYS_CFG_DDR_5_AO_CSR_BASE;
        case 4:
            return SYS_CFG_DDR_4_AO_CSR_BASE;
        case 3:
            return SYS_CFG_DDR_3_AO_CSR_BASE;
        case 2:
            return SYS_CFG_DDR_2_AO_CSR_BASE;
        case 1:
            return SYS_CFG_DDR_1_AO_CSR_BASE;
        case 0:
            return SYS_CFG_DDR_0_AO_CSR_BASE;
        default:
            ASSERT(0, "[lpddrSysCfgGetRegOffset] Non-existing LPDDR module (0-7)");
    }
}

// Asserts/deasserts presetn on the CTL and PRESETn_APB on the PHY
void lpddrModuleApbReset(unsigned int moduleNum, bool resetAssert)
{
  set_reg_u32(lpddrSysCfgGetRegOffset(moduleNum) +  LPDDR_MODULE_APB_RST_OFFSET, (resetAssert) ? 0x00000002 : 0x00000001);
  printf("[lpddrModuleApbReset] DRV_LPDDR: LPDDR CTL APB and PHY APB resets are %s\n", (resetAssert) ? "asserted" : "deasserted");
}

// Asserts/deasserts core_ddrc_rstn and aresetn_0 (AXI) on the CTL
void lpddrCtlCoreReset(unsigned int moduleNum, bool resetAssert)
{
  set_reg_u32(lpddrSysCfgGetRegOffset(moduleNum) + LPDDR_CTL_CORE_RST_OFFSET, (resetAssert) ? 0x00000002 : 0x00000001);
  printf("[lpddrCtlCoreReset] DRV_LPDDR: LPDDR CTL Core and AXI resets are %s\n", (resetAssert) ? "asserted" : "deasserted");
}

// Asserts/deasserts Reset and Reset_async on the PHY
void lpddrPhyReset(unsigned int moduleNum, bool resetAssert)
{
  set_reg_u32(lpddrSysCfgGetRegOffset(moduleNum) + LPDDR_PHY_RST_OFFSET, (resetAssert) ? 0x00000002 : 0x00000001);
  printf("[lpddrPhyReset] DRV_LPDDR: LPDDR PHY reset is %s\n", (resetAssert) ? "asserted" : "deasserted");
}

// Enables/disables LPDDR NOC ht (AXI) fence
void lpddrNocFenceTargHt(unsigned int moduleNum, bool enableFences)
{
  set_range_u32(lpddrSysCfgGetRegOffset(moduleNum) + LPDDR_PPMU_ISOLATION_CONTROL_OFFSET,((enableFences) ? 0x1 : 0x0), 1, 1);
  printf("[lpddrNocFenceTargHt] DRV_LPDDR: LPDDR NOC ht (AXI) fence is %s\n", (enableFences) ? "enabled" : "disabled");
}

// Enables/disables LPDDR NOC cfg (APB) fence
void lpddrNocFenceTargCfg(unsigned int moduleNum, bool enableFences)
{
  set_range_u32(lpddrSysCfgGetRegOffset(moduleNum) + LPDDR_PPMU_ISOLATION_CONTROL_OFFSET,((enableFences) ? 0x1 : 0x0), 0, 0);
  printf("[lpddrNocFenceTargCfg] DRV_LPDDR: LPDDR NOC cfg (APB) fence is %s\n", (enableFences) ? "enabled" : "disabled");
}

// Enables/disables LPDDR AXI low power interface
void lpddrAXILowPowerEnable(unsigned int moduleNum, bool enableLowPower, int idleDelay)
{
  int enable_value = (enableLowPower) ? 0x1 : 0x0;
  int reg_value = idleDelay << 8 | enable_value;
  set_range_u32(lpddrSysCfgGetRegOffset(moduleNum) + LPDDR_CSR_AXI_LOW_POWER_CONTROL_OFFSET, reg_value, 23, 0);
  printf("[lpddrAXILowPower] DRV_LPDDR: low power interface controller for AXI %s\n", (enableLowPower) ? "enabled" : "disabled");
}

// Enables/disables LPDDR DDRC low power interface
void lpddrDDRCLowPowerEnable(unsigned int moduleNum, bool enableLowPower, int idleDelay)
{
  int enable_value = (enableLowPower) ? 0x1 : 0x0;
  int reg_value = idleDelay << 8 | enable_value;
  // Enable the HW low power interface on the CTL IP side
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_HWLPCTL),enable_value,0,0);
  // Enable the HW low power controller in our wrapper.
  set_range_u32(lpddrSysCfgGetRegOffset(moduleNum) + LPDDR_CSR_DDRC_LOW_POWER_CONTROL_OFFSET, reg_value, 23, 0);
  printf("[lpddrDDRCLowPower] DRV_LPDDR: low power interface controller for DDRC %s\n", (enableLowPower) ? "enabled" : "disabled");
}

/* /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ LPDDR PCTL related methods /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ */

/* \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ LPDDR Address Offset methods \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ */

uintptr_t lpddrCtlGetRegOffset(unsigned int moduleNum, uint64_t offset)
{
    ASSERT(moduleNum < 8, "Unsupported model number %d", moduleNum);

    switch(moduleNum) {
        case 7:
            return DDR_7_CTRL_UMCTL2_BASE + offset;
        case 6:
            return DDR_6_CTRL_UMCTL2_BASE + offset;
        case 5:
            return DDR_5_CTRL_UMCTL2_BASE + offset;
        case 4:
            return DDR_4_CTRL_UMCTL2_BASE + offset;
        case 3:
            return DDR_3_CTRL_UMCTL2_BASE + offset;
        case 2:
            return DDR_2_CTRL_UMCTL2_BASE + offset;
        case 1:
            return DDR_1_CTRL_UMCTL2_BASE + offset;
        case 0:
            return DDR_0_CTRL_UMCTL2_BASE + offset;
        default:
            ASSERT(0, "[lpddrCtlGetRegOffset] Non-existing LPDDR module (0-7)");
    }
}

/*
* The need for this function will be removed once we have macro definition
* for all memory-mapped registers within the LPDDR Memory Controller.
*/
static void lpddrCtlWriteReg32(uint64_t offset, uint32_t value)
{
    /* For now fixed to the module instantiated in Veloce */
    set_reg_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, offset), value);
}

uintptr_t lpddrPhyGetRegOffset(unsigned int moduleNum, uint64_t offset)
{
    ASSERT(moduleNum < 8, "Unsupported model number %d", moduleNum);

    switch(moduleNum) {
        case 7:
            return DDR_7_CTRL_PHY_PUB_BASE + (offset << 2);
        case 6:
            return DDR_6_CTRL_PHY_PUB_BASE + (offset << 2);
        case 5:
            return DDR_5_CTRL_PHY_PUB_BASE + (offset << 2);
        case 4:
            return DDR_4_CTRL_PHY_PUB_BASE + (offset << 2);
        case 3:
            return DDR_3_CTRL_PHY_PUB_BASE + (offset << 2);
        case 2:
            return DDR_2_CTRL_PHY_PUB_BASE + (offset << 2);
        case 1:
            return DDR_1_CTRL_PHY_PUB_BASE + (offset << 2);
        case 0:
            return DDR_0_CTRL_PHY_PUB_BASE + (offset << 2);
        default:
            ASSERT(0, "[lpddrPhyGetRegOffset] Non-existing LPDDR module (0-7)");
    }
}

void lpddrPhyWriteReg32(uint64_t offset, uint32_t value)
{
    /* For now fixed to the module instantiated in Veloce */
    set_reg_u32(lpddrPhyGetRegOffset(LPDDR_MODULE_NUM, offset), value);
}

/* /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ LPDDR Address Offset methods /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ */

/* \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ LPDDR Mode register access methods \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ */

// Mode register access information is described in section "10.1 Mode Register Reads and Writes"
// of CTL databook - Version 1.60a-lca00 - May 2024

void lpddrModeRegisterWrite(uint8_t mrAddress, uint8_t mrData){

  printf("[lpddrModeRegisterWrite] MR%0d = 0x%0x\n", mrAddress, mrData);

  // Poll MRSTAT.mr_wr_busy until it is ‘0’
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRSTAT), 0, 0) != 0x0){}

  // Write the MRCTRL0.mr_rank and set MRCTRL0.mr_type to write (0)
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_MRCTRL0, 0x00000030);

  // MRCTRL1.mr_data ([15:8] for MR addr and [7:0] for MR data for write) to define the MR transaction.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL1), mrData + (mrAddress<<8), 15, 0);

  // In a separate APB transaction, write the MRCTRL0.mr_wr to ‘1
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL0), 0x1, 31, 31);

  // Poll MRSTAT.mr_wr_busy until it is ‘0’
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRSTAT), 0, 0) != 0x0){}

}

void lpddrModeRegisterRead(uint8_t mrAddress){

  printf("[lpddrModeRegisterRead] MR%0d\n", mrAddress);

  // If performing MRR and using MRRDATA0/MRRDATA1 registers, write the MRCTRL0.mrr_done_clr to '1'.
  // This bit is self-clearing, and clears the MRSTAT.mrr_done register.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL0), 0x1, 24, 24);

  // Poll MRSTAT.mr_wr_busy until it is ‘0’
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRSTAT), 0, 0) != 0x0){}

  // Write the MRCTRL0.mr_rank and set MRCTRL0.mr_type to read (1)
  // MRR transactions must only be performed to one rank at a time, to avoid bus contention.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL0), 0x1, 5, 4); // set 1 rank
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL0), 0x1, 0, 0); // set to read

  // MRCTRL1.mr_data ([15:8] for MR addr and [7:0] for MR data for write) to define the MR transaction.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL1), (mrAddress<<8), 15, 0);

  // In a separate APB transaction, write the MRCTRL0.mr_wr to ‘1
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRCTRL0), 0x1, 31, 31);

  // Poll MRSTAT.mr_wr_busy until it is ‘0’
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRSTAT), 0, 0) != 0x0){}

  printf("LPDDR_REGB_DDRC_CH0_MRRDATA0 = 0x%lx\n", get_reg_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRRDATA0)));
  printf("LPDDR_REGB_DDRC_CH0_MRRDATA1 = 0x%lx\n", get_reg_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_MRRDATA1)));

}

/* /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ LPDDR Mode register access methods /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ */


void lpddrCtlInit()
{
  printf("[lpddrCtlInit] Programming LPDDR CTL registers\n");
  // Changes based on sw/scripts/lpddr/sequence_modified.txt - generated from local CINIT run with some updates from CPU_DPI SS4 example;
  // Removed FREQ1, FRE2 and FREQ3 register accesses since we are using one frequency for now.
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_MSTR0, 0x03080008);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_DFIMISC, 0x00010005);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_DFIPHYMSTR, 0x80000000);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_DERATECTL1, 0x00000005);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_DERATECTL2, 0x00000005);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_DFIUPD0, 0xc0000000);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_OPCTRL1, 0x00000003); // this is not on the local generated, came from cpu_dpi
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_PWRCTL, 0x00000011);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_INITTMG0, 0x40020002);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_MSTR4, 0x00000101);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFIUPDTMG0, 0x7190000d);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFILPTMG1, 0x00000200);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_TMGCFG, 0x00000001);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG0, 0x28103622);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG1, 0x05100830);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG2, 0x09111117);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG3, 0x000c212f);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG4, 0x0f04040f);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG5, 0x02040c09);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG6, 0x00000012);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG7, 0x00c90003);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG9, 0x00020410);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG12, 0x00030000);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG13, 0x0c100002);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG14, 0x00390320);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG17, 0x00780050);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG24, 0x000f160e);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG25, 0x00002806);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG30, 0x00191318);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_RFSHSET1TMG0, 0x02100061);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_RFSHSET1TMG1, 0x00900090);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_RFSHSET1TMG2, 0x06480000);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_ZQSET1TMG0, 0x001804d6);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_ZQSET1TMG1, 0x02800100);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DERATEVAL0, 0x1024100a);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DERATEVAL1, 0x00000533);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_RANKTMG0, 0x00000b07);
  #ifdef PLATFORM_VELOCE
    lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG0, 0x0337020a); // Previous value was 0x0337021f - changed to match Veloce DFI model
  #else
    lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG0, 0x0337021f);
  #endif
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG1, 0x00080303);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG2, 0x0018371f);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG4, 0x180c0411);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG5, 0x0410000f);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFITMG6, 0x00000117);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_INITMR0, 0x00000000);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DRAMSET1TMG23, 0x009d0009);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_DFIUPDTMG3, 0x00000147);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_RANKTMG1, 0x00001102);
  lpddrCtlWriteReg32(LPDDR_REGB_FREQ0_CH0_RFMSET1TMG0, 0x00000088);
  lpddrCtlWriteReg32(LPDDR_REGB_ARB_PORT0_PCFGW, 0x0000501f); // this is not on the local generated, came from cpu_dpi
  lpddrCtlWriteReg32(LPDDR_REGB_ARB_PORT0_SBRCTL, 0x1000ff10); // this is not on the local generated, came from cpu_dpi
  // Address map is explained at https://git.axelera.ai/prod/europa/-/merge_requests/2005#note_269783
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP1, 0x3f3f3f18);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP3, 0x003f0903);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP4, 0x00000101);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP5, 0x1f030303);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP6, 0x03030300);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP7, 0x1f1f0808);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP8, 0x08080808);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP9, 0x08080808);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP10, 0x08080808);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP11, 0x00000808);
  lpddrCtlWriteReg32(LPDDR_REGB_ADDR_MAP0_ADDRMAP12, 0x00000010);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_OPCTRL1, 0x00000002); // this is not on the local generated, came from cpu_dpi


  // Additional register accesses on static registers (should happen when the ctrl is in reset) unrelated 3 of Table 14-1
  // HWLPTMG
  // Set the delay in 32xDRAM clock cycles between having cactive_in_ddrc going low and cactive_ddrc following.
  // The first is driven by the AXI and SRB being active/idle, the second drives the cactive_ddrc port towards our low power controller
  // The low power controller only starts its idle delay count when cactive_ddrc goes low and send a low power request once the idle delay has been reached
  // When the CTL confirms the low power request through cack_ddr, it stops the core_ddrc_clock.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_FREQ0_CH0_HWLPTMG0),4,HWLPTMG0_hw_lp_idle_x32_BitAddressOffset+HWLPTMG0_hw_lp_idle_x32_RegisterSize,HWLPTMG0_hw_lp_idle_x32_BitAddressOffset);

  // Default number of idle cycle settings, does not strictly have to be set with ctl in reset
  // Set number of idle cycles before automatic self-refresh is entered
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_FREQ0_CH0_PWRTMG),0x01,PWRTMG_selfref_to_x32_BitAddressOffset+PWRTMG_selfref_to_x32_RegisterSize,PWRTMG_selfref_to_x32_BitAddressOffset);
  // Set number of idle cycles before automatic powerdown mode is entered
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_FREQ0_CH0_PWRTMG),0x05,PWRTMG_powerdown_to_x32_BitAddressOffset+PWRTMG_powerdown_to_x32_RegisterSize,PWRTMG_powerdown_to_x32_BitAddressOffset);
}

// Performs step 3 of Table 14-1 DDRCTL and Memory Initialization with LPDDR5X/5/4X PHY
// CTL databook - Version 1.60a-lca00 - May 2024
void lpddrCtlPostCfg(){
  printf("[lpddrCtlPostCfg] Disabling auto-refreshes, self-refresh, powerdown and assertion of dfi_dram_clk_disable\n");
  // RFSHCTL0.dis_auto_refresh = 1
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_RFSHCTL0),1,0,0);
  // PWRCTL.powerdown_en = 0 (For LPDDR4/5 and DDR4, only bit[4] is used.)
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL),0,4,4);
  // PWRCTL.selfref_en = 0 For LPDDR4/5 and DDR4, only bit[0] is used.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL),0,0,0);
  // PWRCTL.en_dfi_dram_clk_disable = 0
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL),0,9,9);

  // Changes added from CPU DPI run (not explained in databook)
  // ZQCTL0.dis_auto_zq
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_ZQCTL0), 0x1, 31, 31);

  // ZQCTL2.dis_srx_zqcl
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_SWCTL, 0x00000000);
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_ZQCTL2), 0x1, 0, 0);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_SWCTL, 0x00000001);
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_SWSTAT), 0, 0) != 0x1){}

}

// Performs step 20 of Table 14-1 DDRCTL and Memory Initialization with LPDDR5X/5/4X PHY
// CTL databook - Version 1.60a-lca00 - May 2024
void lpddrCtlPostPhyInit(){
  printf("[lpddrCtlPostPhyInit] Re-enabling auto-refreshes, self-refresh, powerdown and assertion of dfi_dram_clk_disable\n");

  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_ZQCTL0, 0x00000000);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_SWCTL, 0x00000000);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_ZQCTL2, 0x00000000);
  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_SWCTL, 0x00000001);

  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_SWSTAT), 0, 0) != 0x1){}

  // RFSHCTL0.dis_auto_refresh = 0
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_RFSHCTL0),0,0,0);
  // PWRCTL.powerdown_en = 1 (For LPDDR4/5 and DDR4, only bit[4] is used.)
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL),1,4,4);
  // PWRCTL.selfref_en = 1 For LPDDR4/5 and DDR4, only bit[0] is used.
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL),1,0,0);
  // PWRCTL.en_dfi_dram_clk_disable = 1, this adapted from SNPS config, SNPS has this at 0
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL),1,9,9);

  lpddrCtlWriteReg32(LPDDR_REGB_DDRC_CH0_OPCTRL1, 0x00000000);
  lpddrCtlWriteReg32(LPDDR_REGB_ARB_PORT0_PCTRL, 0x00000001);
}

void lpddrPhyPostInit(){

  // printf("[lpddrPhyPostInit] Inside lpddrPhyPostInit\n");

#ifndef PLATFORM_VELOCE
  // Step 12 - Poll the PUB register MASTER.CalBusy=0
  printf("[lpddrPhyPostInit] Polling DWC_DDRPHYA_ZCAL0_p0_ZCalBusy_AddressOffset\n");
  while(get_range_u16(lpddrPhyGetRegOffset(LPDDR_MODULE_NUM,DWC_DDRPHYA_ZCAL0_p0_ZCalBusy_AddressOffset), 0, 0) == 1){}
#endif // !PLATFORM_VELOCE

  // Step 13 - Set DFIMISC.dfi_init_start to ’1’
  lpddrCtlGroup3Registers(true);
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_DFIMISC), 0x1, 5, 5);
  lpddrCtlGroup3Registers(false);

  // Step 14 - Poll DFISTAT.dfi_init_complete=1
  printf("[lpddrPhyPostInit] Polling DFISTAT.dfi_init_complete=1\n");
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_DFISTAT), 0, 0) == 0){}

  // Step 15 - Set DFIMISC.dfi_init_start to ‘0’
  lpddrCtlGroup3Registers(true);
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_DFIMISC), 0x0, 5, 5);
  // lpddrCtlGroup3Registers(false);

  // Step 16 - update some registers after training
  // TODO: check if this is necessary

  // Step 17 -  Set DFIMISC.dfi_init_complete_en to ‘1’
  // lpddrCtlGroup3Registers(true);
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_DFIMISC), 0x1, 0, 0);
  lpddrCtlGroup3Registers(false);

  // // Step 18 - Set PWRCTL.selfref_sw to ‘0’
  // set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_PWRCTL), 0x0, 11, 11);

  // MODE REGISTER ACCESSES

  // mr_address=18 mr_data=24
  lpddrModeRegisterWrite(18,24);

  // mr_address=1 mr_data=176
  lpddrModeRegisterWrite(1,176);

  // mr_address=2 mr_data=187
  lpddrModeRegisterWrite(2,187);

  // mr_address=3 mr_data=6
  lpddrModeRegisterWrite(3,6);

  // mr_address=10 mr_data=88
  lpddrModeRegisterWrite(10,88);

  // mr_address=11 mr_data=17
  lpddrModeRegisterWrite(11,17);

  // mr_address=12 mr_data=0
  lpddrModeRegisterWrite(12,0);

  // mr_address=13 mr_data=0
  lpddrModeRegisterWrite(13,0);

  // mr_address=14 mr_data=0
  lpddrModeRegisterWrite(14,0);

  // mr_address=15 mr_data=0
  lpddrModeRegisterWrite(15,0);

  // mr_address=17 mr_data=40
  lpddrModeRegisterWrite(17,40);

  // mr_address=19 mr_data=0
  lpddrModeRegisterWrite(19,0);

  // mr_address=20 mr_data=2
  lpddrModeRegisterWrite(20,2);

  // mr_address=22 mr_data=0
  lpddrModeRegisterWrite(22,0);

  // mr_address=23 mr_data=0
  lpddrModeRegisterWrite(23,0);

  // mr_address=25 mr_data=0
  lpddrModeRegisterWrite(25,0);

  // mr_address=28 mr_data=0
  lpddrModeRegisterWrite(28,0);

  // mr_address=37 mr_data=64
  lpddrModeRegisterWrite(37,64);

  // mr_address=40 mr_data=64
  lpddrModeRegisterWrite(40,64);

  // mr_address=41 mr_data=0
  lpddrModeRegisterWrite(41,0);

  // mr_address=46 mr_data=0
  lpddrModeRegisterWrite(46,0);

  // Step 19 - Wait for DWC_ddrctl to move to normal operating mode by monitoring STAT.operating_mode signal
  printf("[lpddrPhyPostInit] Waiting for STAT.operating_mode = 0x1 (normal mode)\n");
  while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_STAT), 0, 0) != 0x1){}

  // Step 20 - Set back registers in step 3 to the original values if desired
  lpddrCtlPostPhyInit();

}

void lpddrCtlGroup3Registers(bool setRegs){

  // Performs software handshake protocol for Group 3 Quasi-dynamic registers
  // Described in Figure 14-2 Software Handshake Protocol and section
  // 14.2.2.3 Group 3: Registers that can be Written When Controller is Empty
  // of CTL databook Version 1.60a-lca00 - May 2024

  printf("[lpddrCtlGroup3Registers] Entering lpddrCtlGroup3Registers method\n");

  if(setRegs) {

    // For multi-port AXI configurations, PCTRL.port_en is used to enable or disable the input traffic per port.
    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_ARB_PORT0_PCTRL), 0x0, 0, 0);

    // The Controller idleness can be polled first from PSTAT register (wr_port_busy_n and rd_port_busy_n bit fields) and should read as PSTAT==32’b0 (not busy).
    // printf("[lpddrCtlGroup3Registers] Waiting for PSTAT == 32'b0\n");
    while(get_reg_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_ARB_PORT0_PSTAT)) != 0x0){}

    // Write 0 to SBRCTL.scrub_en to disable SBR (required only if SBR instantiated).
    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_ARB_PORT0_SBRCTL), 0x0, 0, 0);

    // Poll SBRSTAT.scrub_busy=0, indicates that there are no outstanding SBR read commands (required only if SBR instantiated).
    // printf("[lpddrCtlGroup3Registers] Waiting for SBRSTAT.scrub_busy=0\n");
    while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_ARB_PORT0_SBRSTAT), 0, 0) != 0x0){}

    // OPCTRL1.dis_hif is used to enable or disable the input traffic to the controller.
    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_OPCTRL1), 0x1, 1, 1);

    // Then, DDRC CAM/pipeline empty status must be polled
    // ((OPCTRLCAM.dbg_wr_q_empty== 1’b1) && (OPCTRLCAM.dbg_rd_q_empty== 1’b1) &&
    // (OPCTRLCAM.wr_data_pipeline_empty== 1’b1) && (OPCTRLCAM.rd_data_pipeline_empty== 1’b1)).
    // printf("[lpddrCtlGroup3Registers] Waiting for OPCTRLCAM fields\n");
    while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_OPCTRLCAM), 26, 26) != 0x1){}
    while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_OPCTRLCAM), 25, 25) != 0x1){}
    while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_OPCTRLCAM), 29, 29) != 0x1){}
    while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_OPCTRLCAM), 28, 28) != 0x1){}

    // Set SWCTL.sw_done to zero
    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_SWCTL), 0x0, 0, 0);

    // printf("[lpddrCtlGroup3Registers] Safe to write to the group 3 registers\n");

  } else {
    // printf("[lpddrCtlGroup3Registers] Re-enabling traffic and group 3 registers\n");

    // Set SWCTL.sw_done to 0x1
    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_SWCTL), 0x1, 0, 0);

    // Poll SWSTAT.sw_done_ack == 1
    while(get_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_SWSTAT), 0, 0) != 0x1){}

    // Enable the traffic by writing 1’b1 to PCTRL.port_en or to OPCTRL1.dis_hif if using HIF only. Enable SBR
    // if desired by writing 1’b1 to SBRCTL.scrub_en (only required if SBR instantiated).
    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_ARB_PORT0_PCTRL), 0x1, 0, 0);

    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_OPCTRL1), 0x0, 1, 1);

    set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_ARB_PORT0_SBRCTL), 0x1, 0, 0);

    // printf("[lpddrCtlGroup3Registers] All group 3 registers are re-enabled\n");
  }

}

void lpddrSubsystemInit(bool lowPowerEnable){

  printf("[lpddrSubsystemInit] Starting LPDDR subsystem initialization\n");

  // Disable LPDDR NOC cfg fence for LPDDR subsystem APB interfaces
  lpddrNocFenceTargCfg(LPDDR_MODULE_NUM, LPDDR_NOC_FENCE_DISABLE);

  // Section 14.1.2 Controller Initialization (Controller Databook - Version 1.60a-lca00 - May2024)
  // 4. De-assert presetn once the clocks are active and stable
  lpddrModuleApbReset(LPDDR_MODULE_NUM, LPDDR_RESET_DEASSERT);

  // 5. Allow 128 APB clock cycles for synchronization of presetn to core_ddrc_core_clk and
  // aclk/chi_clk_pn domains and to permit initialization of end logic
  // APB clock @ 800 MHz (1.25 ns)
  // APU clock @ 1200 MHz(0.833333333 ns)
  // 128 * 1.25 = 160
  // 160/0.833333333 = 192.00000007680000003
  cycledelay(200);

  // 6. Initialize the registers
  lpddrCtlInit();

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

  // From Table 14-1 DDRCTL and Memory Initialization with LPDDR5X/5/4X PHY - Step 3
  // NOTE: This was moved after reset due to CPU DPI run (not explained in the databook)
  lpddrCtlPostCfg();

  // From Table 14-1 DDRCTL and Memory Initialization with LPDDR5X/5/4X PHY - Step 5
  // DFIMISC.dfi_init_complete_en and DFIMISC.dfi_reset_n are Quasi-dynamic group 3
  lpddrCtlGroup3Registers(true);
  printf("[lpddrSubsystemInit] DFIMISC.dfi_init_complete_en to 0 and DFIMISC.dfi_reset_n to 1\n");
  // Set DFIMISC.dfi_init_complete_en to ’0’
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_DFIMISC), 0x0, 0, 0);
  // Set DFIMISC.dfi_reset_n to ‘1’
  set_range_u32(lpddrCtlGetRegOffset(LPDDR_MODULE_NUM, LPDDR_REGB_DDRC_CH0_DFIMISC), 0x1, 4, 4);
  lpddrCtlGroup3Registers(false);

  // From Table 14-1 DDRCTL and Memory Initialization with LPDDR5X/5/4X PHY - Steps 6 to 11
  // Start PHY initialization and training by accessing relevant PUB registers from this point onwards
#ifndef PLATFORM_VELOCE
  printf("[lpddrSubsystemInit] Starting PHYinit sequence.\n");
  lpddrPhyInit_cpu_dpi_ss4_skiptrain();
  printf("[lpddrSubsystemInit] PHYinit sequence has ended.\n");
#endif // !PLATFORM_VELOCE

  // From Table 14-1 DDRCTL and Memory Initialization with LPDDR5X/5/4X PHY - Steps 12 to 20
  lpddrPhyPostInit();

  printf("[lpddrSubsystemInit] LPDDR Subsystem intialization is complete\n");

  // Disable LPDDR NOC ht fence for LPDDR subsystem AXI interfaces
  lpddrNocFenceTargHt(LPDDR_MODULE_NUM, LPDDR_NOC_FENCE_DISABLE);

  // Enable the LPDDR CTRL with AXI and DDRC low power interfaces in use. These will stop the AXi and DDRC_core_clk when the ddr is idle
  if(lowPowerEnable) {
    lpddrAXILowPowerEnable(0, true, 5);
    lpddrDDRCLowPowerEnable(0, true, 5);
  }

}

/* \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ LPDDR PHYinit auxiliary methods \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/ */
/*
 * These are auxiliary methods using during the PHYinit sequence of steps.
 * Currently these are not in use since these only take effect for devinit_skiptrain or full training sequence.
 * These are used inside lpddrPhyInitSS3* methods.
*/
void dwc_ddrphy_phyinit_userCustom_wait(uint32_t nDfiClks){
  // DFI clock @ 800 MHz (1.25 ns)
  // APU clock @ 1200 MHz(0.833333333 ns)
  printf("[dwc_ddrphy_phyinit_userCustom_wait] Inside dwc_ddrphy_phyinit_userCustom_wait with %0d DFI clocks\n", nDfiClks);
  if (nDfiClks == 16) {
    // 16 * 1.25 = 20
    // 20/0.833333333 = 24.000000009600000004
    cycledelay(25);
  } else if (nDfiClks == 40) {
    // 40 * 1.25 = 50
    // 50/0.833333333 = 60.00000002400000001
    cycledelay(61);
  }
}

#ifndef PLATFORM_VELOCE
// Based on implementation in sw/scripts/lpddr/synopsys/sim/sw_utilities/phy/software/lpddr5/userCustom/dwc_ddrphy_phyinit_userCustom_G_waitFwDone.c
void dwc_ddrphy_phyinit_getMail(uint16_t* mail, uint16_t* data)
{
  if(mail == NULL) {
    return;
  }

  while(get_range_u16(lpddrPhyGetRegOffset(LPDDR_MODULE_NUM, DWC_DDRPHYA_APBONLY0_UctShadowRegs_AddressOffset), 0, 0) != 0){};
  *mail = get_reg_u16(lpddrPhyGetRegOffset(LPDDR_MODULE_NUM, DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow_AddressOffset));

  if(data != NULL) {
    *data = get_reg_u16(lpddrPhyGetRegOffset(LPDDR_MODULE_NUM, DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow_AddressOffset));
  }

  lpddrPhyWriteReg32(DWC_DDRPHYA_APBONLY0_DctWriteProt_AddressOffset, (uint32_t)0x00000000);
  while(get_range_u16(lpddrPhyGetRegOffset(LPDDR_MODULE_NUM, DWC_DDRPHYA_APBONLY0_UctShadowRegs_AddressOffset), 0, 0) == 0){};
  lpddrPhyWriteReg32(DWC_DDRPHYA_APBONLY0_DctWriteProt_AddressOffset, (uint32_t)0x00000001);
}

// Based on implementation in sw/scripts/lpddr/synopsys/sim/sw_utilities/phy/software/lpddr5/userCustom/dwc_ddrphy_phyinit_userCustom_G_waitFwDone.c
void dwc_ddrphy_phyinit_userCustom_G_waitFwDone()
{
  printf("[dwc_ddrphy_phyinit_userCustom_G_waitFwDone] Inside dwc_ddrphy_phyinit_userCustom_G_waitFwDone\n");

  // Protocol Init
  lpddrPhyWriteReg32(DWC_DDRPHYA_APBONLY0_DctWriteProt_AddressOffset, (uint32_t)0x00000001);
  lpddrPhyWriteReg32(DWC_DDRPHYA_DRTUB0_UctWriteProt_AddressOffset, (uint32_t)0x00000001);

  uint16_t mail = 0;
  while((mail != 0x07) && (mail != 0xff) && (mail != 0x10) && (mail != 0x11)) {
    dwc_ddrphy_phyinit_getMail(&mail, NULL);
    if(mail == 0x08) {
      // dwc_ddrphy_phyinit_getStreamingMessage(mail);
    } else {
      // dwc_ddrphy_phyinit_userCustom_majorMailboxMessage(mail);
    }
  }
}
#endif // !PLATFORM_VELOCE

/* /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ LPDDR PHYinit auxiliary methods /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ */
