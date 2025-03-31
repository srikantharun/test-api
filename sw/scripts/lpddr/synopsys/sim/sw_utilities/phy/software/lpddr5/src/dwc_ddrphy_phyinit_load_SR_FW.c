/**
 * \file
 * \brief loads the save/restore firmware.
 *
 *  \addtogroup SrcFunc
 *  @{
 */
#include <stdio.h>
#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** \brief Loads Save/Restore firmware IMEM and DMEM image
 *
 * This function is used when the Micro-Controller is used to Save/Restore PHY registers.
 * \return void
 */
void dwc_ddrphy_phyinit_load_SR_FW(phyinit_config_t *phyctx)
{

  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;

  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("//##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// Loading Universal Resident Retention FW image\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("//##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("\n");

  uint32_t imem[SR_IMEM_SIZE/sizeof(uint32_t)];
  int imem_offset = 0;
  return_offset_lastaddr_t return_type = return_offset;
  int dmemPerformance;
  uint16_t regData;

  // disable HclkEn if IMEMLoadPerformance is enabled
  uint32_t pmuClkEnables;
  uint8_t pstate = phyctx->runtimeConfig.curPState;
  if(pUserInputAdvanced->IMEMLoadPerfEn){
    pmuClkEnables = 0x0<<csr_HclkEn_LSB | csr_UcclkEn_MASK;
  }else{
    pmuClkEnables = csr_HclkEn_MASK | csr_UcclkEn_MASK;
  }
  if (pUserInputAdvanced->PmuClockDiv[pstate] == 0) {
    pmuClkEnables |= csr_UcclkFull_MASK;
  }
  dwc_ddrphy_phyinit_cmnt(" [%s] Set UcclkHclkEnables = %d\n", __func__, pmuClkEnables);
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  // initialize the dmem structure
  memset(imem, 0, sizeof(imem));

  dwc_ddrphy_phyinit_cmnt(" [%s] Start of loading Universal Resident Retention IMEM\n", __func__);
  imem_offset = dwc_ddrphy_phyinit_storeIncvFile(SR_IMEM_INCV_FILENAME, imem, return_type);
  dmemPerformance = 0;
  // Write local imem array
  dwc_ddrphy_phyinit_WriteOutMem(imem, imem_offset, SR_IMEM_SIZE/sizeof(uint32_t), dmemPerformance);
  //dwc_ddrphy_phyinit_print("WriteImem: COMPLETED\n");
  fflush(stdout);
  dwc_ddrphy_phyinit_cmnt(" [%s] End of loading Universal Resident Retention IMEM\n", __func__);

}

/** @} */
