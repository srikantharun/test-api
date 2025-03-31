/** \file
 *  \brief Implements the register restore portion of S3/IO
 *  \addtogroup SrcFunc
 *  @{
 */

#include "dwc_ddrphy_phyinit.h"

/** \brief This function implements the register restore portion of S3/IO retention sequence.
 *
 * \note This function requires the runtime_config.Reten=1 to enable PhyInit exit retention feature.  This variable can be set as in runtime_config data structure
 * \param phyctx Data structure to hold user-defined parameters
 * \returns 0 on completion of the sequence, EXIT_FAILURE on error.
 */
int dwc_ddrphy_phyinit_restore_sequence(phyinit_config_t *phyctx)
{
  uint16_t regData;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  int NumDbyte = pRuntimeConfig->NumDbyte;
  int numHwPStates = DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;

  if (pRuntimeConfig->RetEn == 0) {
    dwc_ddrphy_phyinit_assert(0, "[%s] retention restore sequence function is called but register save process was not executed during initialization sequence (pRuntimeConfig->RetEn != 0)\n", __func__);
  }


  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s\n", __func__, __func__);
  
	///Before you call this functions perform the following:
	///  --------------------------------------------------------------------------
	///  -# Bring up VDD, VDDQ should already be up
	///  -# Since the CKE* and MEMRESET pin state must be protected, special care
	///    must be taken to ensure that the following signals
	///     - atpg_mode = 1'b0
	///     - PwrOkIn = 1'b0
	///
	///  -# The {BypassModeEn*, WRSTN} signals may be defined at VDD power-on, but
	///    must be driven to ZERO at least 10ns prior to the asserting edge of
	///    PwrOkIn.
	///
	///  -# Start Clocks and Reset the PHY
	///    This step is identical to dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy()
	///
  dwc_ddrphy_phyinit_cmnt("\n");
 dwc_ddrphy_phyinit_cmnt("  Before you call this functions perform the following:\n");
 dwc_ddrphy_phyinit_cmnt("  --------------------------------------------------------------------------\n");
 dwc_ddrphy_phyinit_cmnt("  -# Bring up VDD, VDDQ should already be up\n");
 dwc_ddrphy_phyinit_cmnt("  -# Since the CKE* and MEMRESET pin state must be protected, special care\n");
 dwc_ddrphy_phyinit_cmnt("    must be taken to ensure that the following signals\n");
 dwc_ddrphy_phyinit_cmnt("     - atpg_mode = 1'b0\n");
 dwc_ddrphy_phyinit_cmnt("     - PwrOkIn = 1'b0\n");
 dwc_ddrphy_phyinit_cmnt("\n");
 dwc_ddrphy_phyinit_cmnt("  -# The {BypassModeEn*, WRSTN} signals may be defined at VDD power-on, but\n");
 dwc_ddrphy_phyinit_cmnt("    must be driven to ZERO at least 10ns prior to the asserting edge of\n");
 dwc_ddrphy_phyinit_cmnt("    PwrOkIn.\n");
 dwc_ddrphy_phyinit_cmnt("\n");
 dwc_ddrphy_phyinit_cmnt("  -# Start Clocks and Reset the PHY\n");
 dwc_ddrphy_phyinit_cmnt("    This step is identical to dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy()\n");
 dwc_ddrphy_phyinit_cmnt("\n");

  /// This function performs the following in sequence
  /// --------------------------------------------------------------------------

  /// -# Write the MicroContMuxSel CSR to 0x0 to allow access to the internal CSRs
  dwc_ddrphy_phyinit_cmnt("[%s] Write the MicroContMuxSel CSR to 0x0 to allow access to the internal CSRs\n", __func__);
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(0x0);

  /// -# Write the UcclkHclkEnables CSR to enable all the clocks so the reads can complete
  uint16_t pmuClkEnables = csr_HclkEn_MASK | csr_UcclkEn_MASK;
  uint8_t lowest = 0;

  for (uint32_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    if (((uint32_t)(pUserInputBasic->CfgPStates) & (0x1u << pstate)) == 0){
      continue;
    }

    lowest = pstate;
    break;
  }
  if (pUserInputAdvanced->PmuClockDiv[lowest] == 0){
    pmuClkEnables |= (uint16_t) csr_UcclkFull_MASK;
  }
  dwc_ddrphy_phyinit_cmnt("[%s] Write the UcclkHclkEnables CSR to 0x%x to enable all the clocks so the reads can complete\n", __func__, pmuClkEnables);
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save UcclkHclkEnables to S3 list as if this
  //       CSR is progrmamed at the begining/end of dwc_ddrphy_phyinit_restore_sequence.
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  /// -# Assert ZCalReset to force impedance calibration FSM to idle.
  ///    de-asserted as part of dfi_init_start/complete handshake
  ///    by the PIE when DfiClk is valid.
  ///
  //dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_ZCalReset_ADDR), 0x1);
  regData = 0x1;
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save ZCalReset to S3 list as if this
  //       CSR restored prior to HMZCAL CSR, HMZCAL will not be restored. 
  //       This CSR will be restored at the end of restore sequence
  dwc_ddrphy_phyinit_userCustom_io_write32((tZCAL | csr_ZCalReset_ADDR), regData);

   ///
   // - Program ZcalClkDiv
   //   - Description: Program ZcalClkDiv to 1:1 so PhyInit can write to HMZCAL CSRs (this will be restored in Step I)
   //   - Dependencies:
   //     - None
   ///
  dwc_ddrphy_phyinit_cmnt("[%s] Programming Zcalkclkdiv to 0x%x\n", __func__, 0x0);
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save ZcalClkDiv to S3 list as if this
  //       CSR restored prior to HMZCAL CSR, HMZCAL will not be restored. 
  //       This CSR will be restored at the end of restore sequence
  dwc_ddrphy_phyinit_userCustom_io_write32((tZCAL | csr_ZcalClkDiv_ADDR), 0x0);

  /// -# Issue register writes to restore registers values.
  dwc_ddrphy_phyinit_cmnt("[%s] Issue register writes to restore registers values.\n", __func__);
  dwc_ddrphy_phyinit_cmnt(" --------------------------------------------------\n");
  dwc_ddrphy_phyinit_cmnt(" - IMPORTANT -\n");
  dwc_ddrphy_phyinit_cmnt(" - The register values printed in this txt file are always 0x0. The\n");
  dwc_ddrphy_phyinit_cmnt(" - user must replace them with actual registers values from the save sequence. The\n");
  dwc_ddrphy_phyinit_cmnt(" - save sequence can be found in the output.txt file associated with the particular init sequence.\n");
  dwc_ddrphy_phyinit_cmnt(" - The save sequence issues APB read commands to read and save register values.\n");
  dwc_ddrphy_phyinit_cmnt(" - refer to the init sequence output file for details.\n");
  dwc_ddrphy_phyinit_cmnt(" --------------------------------------------------------------------------------\n");

  // function call for phyinit boot sequence:- write to PwrOkDlyCtrl and VshDacControl
  dwc_ddrphy_phyinit_cmnt("[%s] Issue register writes for power up.\n", __func__);
  dwc_ddrphy_phyinit_PowerUp(phyctx);

  // Enable both DFI channels to read CSRs from either channel
  dwc_ddrphy_phyinit_cmnt("[%s] Enable both DFI channesl to read CSRs from either channel.\n", __func__);
  dwc_ddrphy_phyinit_programDfiMode(phyctx, enableDfiMode);


  dwc_ddrphy_phyinit_cmnt("[%s] Restore S3 register list.\n", __func__);
  dwc_ddrphy_phyinit_regInterface(restoreRegs, 0, 0);

 
  // Restore PubDbyteDisable to all DBYTE's to power down unused DBYTE's
  /**
   * - Program PubDbyteDisable:
   *   - Description: Power down unused DBYTE's
   *   - Dependencies:
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t pubDbyteDis = 0x0u;
  for (uint32_t byte = 0; byte < NumDbyte; byte++) {
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte)) {
      pubDbyteDis |= (0x1u << byte);
  }
  }
     dwc_ddrphy_phyinit_cmnt("[%s] Programming MASTER.PubDbyteDisable to 0x%x\n", __func__, pubDbyteDis);
     // Note: S3 waiver
     //       Purposely using userCustom_io_write32(), do not want to save PubDbyteDisable to S3 list as if this
     //       CSR restored prior to DBYTE CSR, DBYTE will not be restored. 
     //       This CSR will be restored at the end of restore sequence
     dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_PubDbyteDisable_ADDR), pubDbyteDis);
  // Restore ZCalStopClk based on userInput and datarate
  /**
   * - Program ZCalStopClk:
   *   - Description: 
   *   - Fields:
   *     - ZCalStopClk
   *   - Dependencies:
   *     - user_input_advanced.PHYZCalPowerSaving
   */

  for (uint32_t pstate = 0; pstate < numHwPStates; pstate++) {
    //  Data Rate in JEDEC
    uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
    uint16_t ZCalStopClk;
    uint32_t p_addr = pstate << 20;
    if (DataRateMbps <= 3200) {
      ZCalStopClk = (pUserInputAdvanced->PHYZCalPowerSaving == 1) ? 1 : 0;
    
      dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCAL.ZCalStopClk to 0x%x\n", __func__, ZCalStopClk);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save ZCalStopClk to S3 list as if this
      //       CSR restored prior to HMZCAL CSR, HMZCAL will not be restored. 
      //       This CSR will be restored at the end of restore sequence 
      //       dwc_ddrphy_phyinit_restore_sequence.c
      dwc_ddrphy_phyinit_userCustom_io_write32((p_addr | tZCAL | csr_ZCalStopClk_ADDR), ZCalStopClk);
    } 

    /**
     * - Program Seq0BGPR28:
     *   - Description: Set GPR28=0x1 as a one-time flag to be used by PIE during S3 exit
     *   - Dependencies:
     *     - PState 
     */
    regData = 0x1;
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, programming GPR28 to 0x1, for PIE to use during S3 exit\n",  __func__, pstate );
    dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR28_ADDR), regData);
  }

  // Restore DFI channels to userInput based configuration
  dwc_ddrphy_phyinit_cmnt("[%s] Restore DFI channels to userInput based configuration.\n", __func__);
  dwc_ddrphy_phyinit_programDfiMode(phyctx, disableDfiMode);



  /// -# Pulse the TTCF bit to ensure all updates are sent via TTCF
  for (uint32_t byte = 0; byte<(NumDbyte); byte++) {
    uint32_t c_addr = byte << 12;
    // Note: S3 waiver
    //       Purposely using userCustom_io_write32(), do not want to save TtcfForceSendAll to S3 list as this
    //       works by setting to "1" and then setting to  "0",and this CSR will be programmed as below in the dwc_ddrphy_phyinit_restore_sequence.c.
    dwc_ddrphy_phyinit_userCustom_io_write32((tDBYTE | c_addr | csr_TtcfControl_ADDR), (0x1u<<csr_TtcfForceSendAll_LSB));
    dwc_ddrphy_phyinit_userCustom_io_write32((tDBYTE | c_addr | csr_TtcfControl_ADDR), (0x0u<<csr_TtcfForceSendAll_LSB));
  }

 

  /// -# Write the UcclkHclkEnables CSR to disable the appropriate clocks after all reads done.
  dwc_ddrphy_phyinit_cmnt("[%s] Write the UcclkHclkEnables CSR to disable the appropriate clocks after all reads done.\n", __func__);

  dwc_ddrphy_phyinit_cmnt("[%s] Disabling Ucclk (PMU)\n", __func__);
  pmuClkEnables = (csr_HclkEn_MASK | ((pUserInputAdvanced->PmuClockDiv[lowest] == 0) ? csr_UcclkFull_MASK : 0x0));
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save UcclkHclkEnables to S3 list as if this
  //       CSR is progrmamed at the begining/end of dwc_ddrphy_phyinit_restore_sequence.
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);


  /// -# Write the MicroContMuxSel CSR to 0x1 to isolate the internal CSRs during mission mode
  regData = 0x1;
  dwc_ddrphy_phyinit_cmnt("[%s] Write the MicroContMuxSel CSR to 0x1 to isolate the internal CSRs during mission mode\n", __func__);
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(regData);
  
	///After Function Call
	///  --------------------------------------------------------------------------
	///  To complete the Retention Exit sequence:
	///
	///  -# Initialize the PHY to Mission Mode through DFI Initialization
	///    You may use the same sequence implemented in
	///    dwc_ddrphy_phyinit_userCustom_J_enterMissionMode()
	///
  dwc_ddrphy_phyinit_cmnt("\n");
 dwc_ddrphy_phyinit_cmnt("  After Function Call\n");
 dwc_ddrphy_phyinit_cmnt("  --------------------------------------------------------------------------\n");
 dwc_ddrphy_phyinit_cmnt("  To complete the Retention Exit sequence:\n");
 dwc_ddrphy_phyinit_cmnt("\n");
 dwc_ddrphy_phyinit_cmnt("  -# Initialize the PHY to Mission Mode through DFI Initialization\n");
 dwc_ddrphy_phyinit_cmnt("    You may use the same sequence implemented in\n");
 dwc_ddrphy_phyinit_cmnt("    dwc_ddrphy_phyinit_userCustom_J_enterMissionMode()\n");
 dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("[%s] End of %s\n", __func__, __func__);
  return 0;
}


/** \brief Program PowerDown CSRs
 *
 * \note This function programs all the power down CSRs to power up/down the IOs
 *
 * \param powerDown 0: power up all CSRs, 1: power down all CSRs
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns void
 */
void dwc_ddrphy_phyinit_setTxRxPowerDown(uint8_t powerDown, phyinit_config_t *phyctx) {
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  uint8_t NumHmacPerChan = NUM_HMAC_PER_CHAN;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive;
  uint8_t DtoEnable = pUserInputAdvanced->DtoEnable;


  /**
   * - Program RxPowerDownAC and ACXPowerDownLn{0,1}
   *   - Description:
   *     - LPDDR5:
   *       - RX - power down all lanes
   *       - TX - no txpowerdown in lp5x phy, they don't use DACs, so nothing to save when not driving
   *     - DDR5:
   *       - RX - power down all lanes except ALERT lanes
   *       - TX - power down MTEST lane
   *   - Fields:
   *     - AcTxPowerDownLn{0,1}
   *     - RxPowerDownAC
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   */

   uint16_t RxPowerDownAC   = csr_RxPowerDownAC_MASK;

   // Rx PowerDown - for LPDDR5, power down all Rx lanes
  for (int acx=0; acx<NumAchnActive; acx++) {
    for (int hmac=0; hmac<NumHmacPerChan; hmac++) {
      uint32_t c_addr = (hmac + acx*NumHmacPerChan)*c1;
      int instance = hmac + acx*NumHmacPerChan;

      _SKIP_DIFF_CK1_LP5_LP4_ONLY(hmac)

      dwc_ddrphy_phyinit_cmnt("[%s] Programming ACX%d HMAC%d Instance%d RxPowerDownAC to 0x%x\n",  __func__, acx, hmac, instance, RxPowerDownAC);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save RxPowerDownAC to S3 list as if this
      //       CSR is progrmamed at the beginning of dwc_ddrphy_phyinit_restore_sequence.
      dwc_ddrphy_phyinit_userCustom_io_write32((tHMAC | c_addr | csr_RxPowerDownAC_ADDR), RxPowerDownAC);
      _PROG_DTO(DtoEnable, acx, hmac, "RxPowerDownAC",(tHMAC | c14 | csr_RxPowerDownAC_ADDR), RxPowerDownAC)
    }
  }





  /**
   * - Program TxPowerDownZCAL
   *   - Description: Power up or down on HMZCAL
   *   - Fields:
   *     - TxPowerDownZCAL
   *   - Dependencies:
   *     - None
   */
  uint16_t TxPowerDownZCAL = (powerDown == 1) ? (2u << csr_TxPowerDownZCAL_LSB) : (0u << csr_TxPowerDownZCAL_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming HMZCAL TxPowerDownZCAL to 0x%x\n", __func__, TxPowerDownZCAL);

  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save TxPowerDownZCAL to S3 list as if this
  //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
  dwc_ddrphy_phyinit_userCustom_io_write32((tHMZCAL | csr_TxPowerDownZCAL_ADDR), TxPowerDownZCAL);

  /**
   * - Program ZcalPowerCtl
   *   - Description: When RxPowerDown is set, enables RxPowerDown on the ZCAL Receiver. When RxStandby is set, enables RxStandby on the ZCAL Receiver.
   *   - Fields: RxPowerDown, RxStandby
   *   - Dependencies:
   */
  uint16_t ZcalPowerCtl = 0x1u << csr_RxPowerDown_LSB;
  dwc_ddrphy_phyinit_cmnt("[%s] Programming HMZCAL ZcalPowerCtl.RxPowerDown to 0x%x\n",  __func__, ZcalPowerCtl);
  dwc_ddrphy_phyinit_io_write32((tHMZCAL | csr_ZcalPowerCtl_ADDR), ZcalPowerCtl);

  /**
   * - Program DxRxPowerDownLn{0..4} and DxRxPowerDownDQS
   *   - Description: Power up or down HMDBYTE lanes
   *   - Fields:
   *     - TxPowerDownLn0
   *     - RxPowerDownLn0
   *   - Dependancies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t TxRxPowerDownLnX = (powerDown == 1) ? (2u << csr_TxPowerDownLn0_LSB | 1u << csr_RxPowerDownLn0_LSB) : (0u << csr_TxPowerDownLn0_LSB | 0u << csr_RxPowerDownLn0_LSB);
  uint16_t TxRxPowerDownDQS0 = (powerDown == 1) ? (2u << csr_TxPowerDownDQS_LSB | 1u << csr_RxPowerDownDQS_LSB) : (0u << csr_TxPowerDownDQS_LSB | 0u << csr_RxPowerDownDQS_LSB);
  uint16_t TxRxPowerDownDQS1 = (powerDown == 1) ? (2u << csr_TxPowerDownDQS_LSB | 1u << csr_RxPowerDownDQS_LSB) : (0u << csr_TxPowerDownDQS_LSB | 0u << csr_RxPowerDownDQS_LSB);


  for (int byte=0; byte < NumDbyteActive; byte++) {
    int c_addr0 = ((byte*2) & 0xf) * c1;
    int c_addr1 = (((byte*2)+1) & 0xf)* c1;

      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence. 
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX0 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 0, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr0 | csr_DxRxPowerDownLn0_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence. 
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX0 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 1, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr0 | csr_DxRxPowerDownLn1_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence. 
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX0 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 2, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr0 | csr_DxRxPowerDownLn2_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence. 
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX0 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 3, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr0 | csr_DxRxPowerDownLn3_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX1 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 0, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr1 | csr_DxRxPowerDownLn0_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX1 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 1, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr1 | csr_DxRxPowerDownLn1_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX1 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 2, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr1 | csr_DxRxPowerDownLn2_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX1 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 3, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr1 | csr_DxRxPowerDownLn3_ADDR), TxRxPowerDownLnX);
      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownLn* to S3 list as if this
      //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX1 DxRxPowerDownLn%d TxPowerDown to 0x%x\n",  __func__, byte, 4, TxRxPowerDownLnX);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr1 | csr_DxRxPowerDownLn4_ADDR), TxRxPowerDownLnX);
    TxRxPowerDownDQS0 = (powerDown == 1) ? (2u << csr_TxPowerDownDQS_LSB | 1u << csr_RxPowerDownDQS_LSB) : (2u << csr_TxPowerDownDQS_LSB | 0u << csr_RxPowerDownDQS_LSB);
    TxRxPowerDownDQS1 = (powerDown == 1) ? (2u << csr_TxPowerDownDQS_LSB | 1u << csr_RxPowerDownDQS_LSB) : (0u << csr_TxPowerDownDQS_LSB | 1u << csr_RxPowerDownDQS_LSB);

    // Note: S3 waiver
    //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownDQS to S3 list as if this
    //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX0 DxRxPowerDownDQS TxPowerDown to 0x%x\n",  __func__, byte, TxRxPowerDownDQS0);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr0 | csr_DxRxPowerDownDQS_ADDR), TxRxPowerDownDQS0);
    // Note: S3 waiver
    //       Purposely using userCustom_io_write32(), do not want to save DxRxPowerDownDQS to S3 list as if this
    //       CSR is progrmamed/set at the begining of dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_cmnt("[%s] Programming HMDBYTE%d DX1 DxRxPowerDownDQS TxPowerDown to 0x%x\n",  __func__, byte, TxRxPowerDownDQS1);
    dwc_ddrphy_phyinit_userCustom_io_write32((tHMDBYTE | c_addr1 | csr_DxRxPowerDownDQS_ADDR), TxRxPowerDownDQS1);
    }


  

}

/** \brief Power up sequence for PhyInit
 *
 * \note This function implements the register programming for power up sequence
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns void
 */
void dwc_ddrphy_phyinit_PowerUp(phyinit_config_t *phyctx) {
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  uint8_t NumAchn = pUserInputBasic->NumCh;


  int numHwPStates = DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;

  /**
   * - Program TxImpedanceAC
   *   - Description: Program chip select TxImpedance to default value 50 0hms , TxImpedance CK to default value 30 0hms
   *   - Fields:
   *     - TxStrenCodePUAC
   *     - TxStrenCodePDAC
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   */
  // Program TxImpedanceAC CS
  uint16_t TxImpedance = (0xfU << csr_TxStrenCodePUAC_LSB) | (0xfU << csr_TxStrenCodePDAC_LSB);

  for (uint32_t ps = 0; ps < numHwPStates; ps++) {
    uint16_t TxImpedanceCk = (0x7u << csr_TxStrenCodePUAC_LSB) | (0x7u << csr_TxStrenCodePDAC_LSB);
    uint32_t p_addr = ps << 20;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMAC 4  TxImpedanceAC::CS to 0x%x\n", __func__, ps, TxImpedance);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c4 | csr_TxImpedanceAC_ADDR), TxImpedance);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMAC 5  TxImpedanceAC::CK to 0x%x\n", __func__, ps, TxImpedanceCk);
    dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c5 | csr_TxImpedanceAC_ADDR), TxImpedanceCk);
    if(NumAchn > 1){
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMAC 11 TxImpedanceAC::CS to 0x%x\n", __func__, ps, TxImpedance);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c11 | csr_TxImpedanceAC_ADDR), TxImpedance);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming HMAC 12 TxImpedanceAC::CK to 0x%x\n", __func__, ps, TxImpedanceCk);
      dwc_ddrphy_phyinit_io_write32((p_addr | tHMAC | c12 | csr_TxImpedanceAC_ADDR), TxImpedanceCk);
    }
  }

  /**
   * - Call dwc_ddrphy_phyinit_setTxRxPowerDown to power down the IOs
   */
  dwc_ddrphy_phyinit_setTxRxPowerDown(1, phyctx);

  /**
   * - Program PorControl
   *   - Description: Program PwrOkDlyCtrl to enable the PwrOk_VDD/PwrOk_VDDQ/PwrOk_VAA as part of power up sequence
   *   - Fields:
   *     - PwrOkDlyCtrl
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   */
  int PorControl;

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PorControl::PwrOkDlyCtrl to 1'b1\n", __func__);
  PorControl = 0x0001u << csr_PwrOkDlyCtrl_LSB;
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save PorControl to S3 list as if this
  //       CSR is dynamic progrmamed/set during PIE sequence and dwc_ddrphy_phyinit_restore_sequence.
  dwc_ddrphy_phyinit_userCustom_io_write32((tAC | c0 | csr_PorControl_ADDR), PorControl);

  if (NumAchn > 1) {
    // Note: S3 waiver
    //       Purposely using userCustom_io_write32(), do not want to save PorControl to S3 list as if this
    //       CSR is dynamic progrmamed/set during PIE sequence and dwc_ddrphy_phyinit_restore_sequence.
    dwc_ddrphy_phyinit_userCustom_io_write32((tAC | c1 | csr_PorControl_ADDR), PorControl);
  }

    // Wait 16 DfiClk's for meeting the requirement of 1ns delay between pwrokdlyctrl and VshCtrlUpdate even in case of dfi clk skew enabled
    dwc_ddrphy_phyinit_userCustom_wait(16);


  /**
   * - Call dwc_ddrphy_phyinit_setTxRxPowerDown to power up the IOs
   */
  dwc_ddrphy_phyinit_setTxRxPowerDown(0, phyctx);

}

/** @} */
