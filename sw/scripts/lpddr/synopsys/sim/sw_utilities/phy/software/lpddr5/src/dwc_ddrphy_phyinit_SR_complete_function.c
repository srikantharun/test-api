/**
 * \file
 * \brief End of Micro-Controller based Save/Restore function.
 *
 * This file contains the implementation of dwc_ddrphy_phyinit_SR_complete_function
 * function.
 *
 *  \addtogroup SrcFunc
 *  @{
 */
#include "dwc_ddrphy_phyinit.h"

/** \brief End of Micro-Controller based Save/Restore function.
 *
 * This function Halts the Micro Controller, Gate clocks in prepration for
 * mission mode during for the Micro Controller based Save/Restore sequence.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */
void dwc_ddrphy_phyinit_SR_complete_function(phyinit_config_t *phyctx)
{
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint8_t pstate = pRuntimeConfig->curPState;
  uint16_t regData;

  dwc_ddrphy_phyinit_cmnt("\n\n");
  dwc_ddrphy_phyinit_cmnt("//##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// 5.3 Initialize PHY Configuration\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// Optional step (SR) - Save Complete\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// Required PHY registers saved to DMEM for later IO retention exit restore performed by firmware\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("//##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n\n");

  dwc_ddrphy_phyinit_cmnt(" [%s] Start of %s\n", __func__, __func__);

  //##############################################################
  //
  // To Halt Micro Controller after save operation completed
  // CSRs to program:
  //   MicroReset
  //
  //##############################################################
  regData = 0x1 << csr_StallToMicro_LSB;
  dwc_ddrphy_phyinit_cmnt("// Halt Micro Controller.\n");
  dwc_ddrphy_phyinit_userCustom_io_write32((tAPBONLY | csr_MicroReset_ADDR), regData);

  //##############################################################
  //
  // To gain control of the APB bus
  // To gate the micro controller clock and/or training hardware clock accordingly
  // To isolate the APB bus access
  // CSRs to program:
  //   MicroContMuxSel UcclkHclkEnables
  //
  //##############################################################
  regData = 0x0;
  dwc_ddrphy_phyinit_cmnt("// Enable access to the internal CSRs by setting the MicroContMuxSel CSR to 0.\n");
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(regData);

  // LPDDR4 will need ACSM for PPT, and thus not gating Hclk (only gates Ucclk)
  dwc_ddrphy_phyinit_cmnt("// Disabling Ucclk (PMU)\n");
  uint16_t pmuClkEnables = csr_HclkEn_MASK | 0x0<<csr_UcclkEn_LSB;

  if (pUserInputAdvanced->PmuClockDiv[pstate] == 0) {
    pmuClkEnables |= csr_UcclkFull_MASK;
  }
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  regData = 0x1;
  dwc_ddrphy_phyinit_cmnt("// Isolate the APB access from the internal CSRs by setting the MicroContMuxSel CSR to 1.\n");
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(regData);

  //##############################################################
  //##############################################################
  dwc_ddrphy_phyinit_cmnt(" [%s] End of %s\n", __func__, __func__);
}

// End of dwc_ddrphy_phyinit_SR_complete_function()
/** @} */
