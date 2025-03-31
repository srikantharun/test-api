
/** \file
 * \brief implements Step I of initialization sequence
 *
 * This file contains the implementation of dwc_ddrphy_phyinit_I_initPhyConfig
 * function.
 *
 *  \addtogroup SrcFunc
 *  @{
 */
#include <math.h>
#include <stdlib.h>
#include "dwc_ddrphy_phyinit.h"
#include "dwc_ddrphy_phyinit_LoadPieProdCode.h"

/*! \def PIE_START_CSR_ADDR
 * \brief Starting CSR address of PIE SRAM
 */
#define PIE_START_CSR_ADDR (0x44000u)

/*! \def ACSM_MRW_START_ADDR
 * \brief Starting CSR address of MRM instructions in ACSM SRAM.
 */
#define ACSM_MRW_START_ADDR (ACSM_NOP_ROW_OFFSET * 4)  // placed after NOP used for skipMRW

/*! \def ACSM_MRW_INSTRU_NUM_PER_PSTATE
 * \brief Number of ACSM MRW instructions per PState.
 */
#define ACSM_MRW_INSTRU_NUM_PER_PSTATE 148

extern int acsmClkRatio; 
int acsmClkRatio;                             ///< ACSM clock ratio
extern uint16_t acsmInstPtr;
uint16_t acsmInstPtr = ACSM_MRW_START_ADDR;   ///< ACSM SRAM instruction pointer

static void loadAcsmMRW(phyinit_config_t *phyctx, int inPsLoop);


/** \brief Loads registers after training
 *
 * This function programs the PHY Initialization Engine (PIE) instructions and
 * the associated registers.
 * Training hardware registers are also programmed to for mission mode
 * retraining.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 *
 * Detailed list of registers programmed by this function:
 */
void dwc_ddrphy_phyinit_I_loadPIEImage(phyinit_config_t *phyctx)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint8_t pstate = pRuntimeConfig->curPState;
  uint8_t prog_csr = (pRuntimeConfig->initCtrl & 0x1u) >> 0;
  uint8_t skip_pie = (pRuntimeConfig->initCtrl & 0x10u) >> 4;
  uint16_t regData;

  uint8_t NumAchn = pUserInputBasic->NumCh;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;

  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;

  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s() prog_csr=%d\n", __func__, __func__, prog_csr);
  initRuntimeConfigEnableBits(phyctx);

  if (skip_pie) {
    dwc_ddrphy_phyinit_cmnt("[%s] skip_pie flag set. Skipping %s\n", __func__, __func__);
    return;
  }

  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt(" (I) Load PHY Init Engine Image\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("Load the PHY Initialization Engine memory with the provided initialization sequence.\n");
  dwc_ddrphy_phyinit_cmnt("See PhyInit App Note for detailed description and function usage\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt(" For LPDDR4/LPDDR5, this sequence will include the necessary retraining code.\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("##############################################################\n");
  dwc_ddrphy_phyinit_cmnt("\n");
  dwc_ddrphy_phyinit_cmnt("\n");

  // reset the acsm instruction Ptr (leave room for NOP pair)
  acsmInstPtr = ACSM_MRW_START_ADDR;

  /**
   * - Program MicroContMuxSel:
   *   - Description: Enalbe access to internal CSRs by setting to 0
   *   - Dependencies:
   *     - None
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Enable access to the internal CSRs by setting the MicroContMuxSel CSR to 0.\n", __func__);
  dwc_ddrphy_phyinit_cmnt("[%s] This allows the memory controller unrestricted access to the configuration CSRs.\n", __func__);
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(0x0);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PIE Production Code\n",  __func__);

  dwc_ddrphy_phyinit_LoadPieProdCode(phyctx);

  // Moving this programming of PPGC CSR, since we need to disable MRs DLEP/System Link ECC feature without affecting PPT2 retraining on DMI pin.
  // Update PPT2 specific CSRs if enabled
  uint16_t ppt2Enabled   = 0x0;
  uint16_t DMIPinPresent = 0x0;
  uint32_t cfgPStates = pUserInputBasic->CfgPStates;

  for (uint32_t ps=0; ps<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; ps++) {
    // Skip disabled PStates
    if ((cfgPStates & (0x1u << ps)) == 0) {
      continue;
    }

    // Check if any PState has PPT2 enabled
    if (pUserInputAdvanced->RetrainMode[ps] == 0x4) {
      ppt2Enabled = 0x1;
    }

    // Check MR3[6] for DBI-RD or MR22[7:6] for RECC
    if ((((mb1D[ps].MR3_A0 & 0x40u) >> 6u & 1u) | ((mb1D[ps].MR22_A0 & 0xC0u) >> 6u & 1u))) {
      DMIPinPresent = 0x1;
    }
  }

  // If PPT2 and DMI pin is present, program PPGC CSR for PPT2
  if ((ppt2Enabled == 0x1) && (DMIPinPresent == 0x1)) {
    /**
     * - Program PpgcGenDbiCtrl:
     *   - Description: If DBI-RD (LP4X/5/5X) or RECC (LP5/5X) enabled, enable PPGC DM mode for PPT2
     *   - Dependencies:
     *     - user_input_advanced.RetrainMode
     *     - user_input_basic.DramType
     *     - mb1D[ps].MR3[DBI-RD] (LP4X/5/5X)
     *     - mb1D[ps].MR22[RECC]  (LP5/5X)
     */
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming PpgcGenDbiCtrl to 0x%x\n", __func__, pstate, csr_PpgcGenDmMode_MASK);
    dwc_ddrphy_phyinit_io_write32(c0 | tPPGC | csr_PpgcGenDbiCtrl_ADDR, csr_PpgcGenDmMode_MASK);
  }


  // Load each PState MRW in order, skip if DisableFspOp=1 since PIE is not resposible for FSP switching
  if (pUserInputAdvanced->DisableFspOp != 1) {
    loadAcsmMRW(phyctx, 0);
  }



  /**
   * - Program SequenceOverride, PieVecCfg, PieInitVecSel:
   *   - Description: Set SequenceOverride[SelectDFIFreqToGPRMux]=1 to use dfi_freq bug for PIE WR using GPR0, program PieVecCfg/PieInitVecSel PIE start vectors
   *   - Fields:
   *     - SelectDFIFreqToGPRMux
   *     - BlockSeq0BRequests
   *     - PieInitStartVec0
   *     - PieInitStartVec1
   *     - PieInitStartVec2
   *     - PieInitStartVec3
   *     - PieInitVecSel0
   *     - PieInitVecSel1
   *     - PieInitVecSel2
   *     - PieInitVecSel3
   *   - Dependencies:
   *     - None
   */
  // set BlockSeq0BRequests to 0
  regData = 0x1UL << csr_SelectDFIFreqToGPRMux_LSB;
  dwc_ddrphy_phyinit_io_write32((tAPBONLY | csr_SequencerOverride_ADDR), regData);

  regData = (0x5UL << csr_PieInitVecSel3_LSB) | (0x8UL << csr_PieInitVecSel2_LSB) | (0x2UL << csr_PieInitVecSel1_LSB) | (0x1UL << csr_PieInitVecSel0_LSB);
  dwc_ddrphy_phyinit_io_write32((tDRTUB | csr_PieInitVecSel_ADDR), regData);

  dwc_ddrphy_phyinit_PieFlags(phyctx, prog_csr);

  /**
   * - Program FspSkipList:
   *   - Description: Program destPState values that to not update the FspState for PIE FSP switching
   *   - Fields:
   *     - FspPStateSkip0
   *     - FspPStateSkip1
   *     - FspPStateSkip2
   *     - FspPStateSkip3
   *   - Dependencies:
   *     - None
   */
  regData = (0x5UL << csr_FspPStateSkip3_LSB) | (0x5UL << csr_FspPStateSkip2_LSB) | (0x5UL << csr_FspPStateSkip1_LSB) | (0x5UL << csr_FspPStateSkip0_LSB);
  dwc_ddrphy_phyinit_io_write32((tPPGC | csr_FspSkipList_ADDR), regData);


  // Program training hardware registers for mission mode retraining and DRAM drift compensation algorithm
  dwc_ddrphy_phyinit_cmnt("[%s] Programing Training Hardware Registers for mission mode retraining\n", __func__);
  if (prog_csr == 0) {
    dwc_ddrphy_phyinit_cmnt("[%s] Enabling Phy Master Interface for DRAM drift compensation\n", __func__);
    dwc_ddrphy_phyinit_ProgPPT(phyctx);
  }


  /**
   * - Program HwtControlVal:
   *   - Description: Program override bits for outputs of ACSM used by DFI0 and DFI1
   *   - Fields:
   *     - HwtCs0Val0
   *     - HwtCs0Val1
   *     - HwtCs1Val0
   *     - HwtCs1Val1
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumRank_dfi0
   *     - user_input_basic.NumRank_dfi1
   *     - user_input_basic.NumCh
   */
  regData = csr_HwtCs0Val0_MASK;

  if (pUserInputBasic->NumRank_dfi0 == 2){
    regData |= csr_HwtCs1Val0_MASK;
  }

  if (pUserInputBasic->NumCh > 1) {
    regData |= csr_HwtCs0Val1_MASK;
    if (pUserInputBasic->NumRank_dfi1 == 2){
      regData |= csr_HwtCs1Val1_MASK;
    }
  }

  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_HwtControlVal_ADDR), regData);

  /**
   * - Program FspState:
   *   - Description: Program capture of the state of status interface fore retention enter/exit
   *   - Fields:
   *     - DramFsp2xPhyPs
   *     - DramFsp1xPhyPs
   *     - DramFsp0xPhyPs
   *   - Dependencies:
   *     - None
   */
  regData = (0x1fUL << csr_DramFsp2xPhyPs_LSB) | (0x1fUL << csr_DramFsp1xPhyPs_LSB) | (0x1fUL << csr_DramFsp0xPhyPs_LSB);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_FspState_ADDR), regData);


  /**
   * - Program ForceClkDisable:
   *   - Description: Prepare for cold boot by setting the ForceClkDisable to prevent glitches on Ck's
   *   - Dependencies:
   *     - user_input_basic.NumCh
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Programming AC0 ForceClkDisable to 0x%x\n", __func__, 0x1);
  dwc_ddrphy_phyinit_io_write32((tAC | c0 | csr_ForceClkDisable_ADDR), (0x1u<<csr_ForceClkDisable_LSB));

  if (NumAchn>1 && NumAchnActive>1) {
    dwc_ddrphy_phyinit_cmnt("[%s] Programming AC1 ForceClkDisable to 0x%x\n", __func__, 0x1);
    dwc_ddrphy_phyinit_io_write32((tAC | c1 | csr_ForceClkDisable_ADDR), (0x1u<<csr_ForceClkDisable_LSB));
  }


  /// - Register
  ///   - ACSMParityInvert, ACSMCkeControl, ACSMInfiniteOLRC, ACSMDefaultAddr,
  ///     ACSMDefaultCs, ACSMStaticCtrl, ACSMLowSpeedClockEnable, ACSMLowSpeedClockDelay
  /// - Set D5 ACSM CSRs that FW may have configured to ensure no affects on D5 PPT
  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMParityInvert = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMParityInvert_ADDR), 0x0);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMCkeControl = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMCkeControl_ADDR), 0x0);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMInfiniteOLRC = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMInfiniteOLRC_ADDR), 0x0);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMDefaultAddr = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMDefaultAddr_ADDR), 0x0);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMDefaultCs = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMDefaultCs_ADDR), 0x0);

  regData = (0x0uL << csr_ACSMPhaseControl_LSB);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMStaticCtrl = 0x%x\n", __func__, regData);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMStaticCtrl_ADDR), regData);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMLowSpeedClockEnable = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMLowSpeedClockEnable_ADDR), 0x0);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming PPGC ACSMLowSpeedClockDelay = 0x%x\n", __func__, 0x0);
  dwc_ddrphy_phyinit_io_write32((c0 | tPPGC | csr_ACSMLowSpeedClockDelay_ADDR), 0x0);




  



  // Disable DFI channels based on userInput
  dwc_ddrphy_phyinit_programDfiMode(phyctx, disableDfiMode);

  /**
   * - Program UcclkHclkEnables:
   *   - Description: Set the HclkeEn, UcclkEn, UcclkFull, at the end of Step I, clock gate UcClk, keep HclkEn enabled for PIE to do cold boot
   *   - Fields:
   *     - HclkEn
   *     - UcclkEn
   *     - UcclkFull
   *   - Dependencies:
   *     - user_input_advanced.PmuClockDiv
   */
  
  dwc_ddrphy_phyinit_cmnt("[%s] Disabling Ucclk (PMU)\n", __func__);
  uint16_t pmuClkEnables = csr_HclkEn_MASK | 0x0u<<csr_UcclkEn_LSB;

  if (pUserInputAdvanced->PmuClockDiv[pstate] == 0) {
    pmuClkEnables |= csr_UcclkFull_MASK;
  }
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save pmuClkEnables to S3 list as if this
  //       CSR dynamic changed. pmuClkEnables is also progrmamed/set at the begining/end of dwc_ddrphy_phyinit_restore_sequence.c to enable clocks.
  dwc_ddrphy_phyinit_userCustom_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  dwc_ddrphy_phyinit_cmnt("[%s] Isolate the APB access from the internal CSRs by setting the MicroContMuxSel CSR to 1.\n", __func__);
  dwc_ddrphy_phyinit_MicroContMuxSel_write32(0x1);

  dwc_ddrphy_phyinit_cmnt("[%s] End of %s()\n",  __func__, __func__);
}  // End of dwc_ddrphy_phyinit_I_loadPIEImage



/** \brief Loads registers after training
 *
 * This is a helper function to program PPT registers.It is called by dwc_ddrphy_phyinit_I_loadPIEImage().
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 *int
 * Detailed list of registers programmed by this function:
 */
void dwc_ddrphy_phyinit_ProgPPT(phyinit_config_t *phyctx)
{
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint16_t regData;
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive;
  
  for (int byte = 0; byte < NumDbyteActive; byte++) { // for each chiplet
    uint32_t c_addr = byte * c1;

    /**
     * - Program DtsmGoodBar:
     *   - Description: Program the DTSM accumulator upper threshold
     *   - Dependencies:
     *     - user_input_basic.NumDbytesPerCh
     */
    regData = 0x1;
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_DtsmGoodBar_ADDR), regData); // [15:0] good_bar;
    regData = (csr_DtsmStaticCmpr_MASK | csr_DtsmStaticCmprVal_MASK);

    /**
     * - Program DtsmByteCtrl1, DtsmErrBar:
     *   - Description: Program DTSM sample input select/mode control and DtsmErrBar sets DTSM accumulator lower threshold
     *   - Fields:
     *     - DtsmIncDecMode
     *     - DtsmStaticCmpr
     *     - DtsmStaticCmprVal
     *   - Dependencies:
     *     - user_input_basic.NumDbytesPerCh
     */
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_DtsmByteCtrl1_ADDR), regData);
    regData = 0x1;
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_DtsmErrBar_ADDR), regData); // [15:0] bad_bar;


    /**
     * - Program PptRxEnEvent:
     *   - Description: Program PptRxEnEvnt to reset value after Training FW is complete
     *   - Fields: None
     *   - Dependencies: None
     */
    regData = 0;
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_PptRxEnEvnt_ADDR), regData);


    /**
     * - Program DtsmLaneCtrl0:
     *   - Description: DTSM armed and sensitive for ddr_rxval
     *   - Fields:
     *     - DtsmEnb
     *   - Dependencies:
     *     - user_input_basic.NumDbytesPerCh
     */
    regData = (0x1u << csr_DtsmEnb_LSB);
    dwc_ddrphy_phyinit_io_write32((c_addr | i0 | tDBYTE | csr_DtsmLaneCtrl0_ADDR), regData);


    /**
     * - Program Prbs0GenStateHi, Prbs0GenStateLo, Prbs0ChkStateHi, Prbs0ChkStateLo:
     *   - Description: Configure the PPGC pattern used for PPT2 RxClk and TxDQ
     *   - Fields:
     *     - Prbs0GenStateHi, Prbs0GenStateLo, Prbs0ChkStateHi, Prbs0ChkStateLo
     *   - Dependencies:
     *     - None
     */
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_Prbs0ChkStateHi_ADDR), 0x5a3c); // TX Chk pattern high
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_Prbs0ChkStateLo_ADDR), 0x5a3c); // TX Chk pattern low

    /**
     * - Program Prbs0GenModeSel, Prbs0ChkModeSel:
     *   - Description: Configure the PPGC to be pattern mode when used for PPT2 RxClk and TxDQ
     *   - Fields:
     *     - Prbs0GenModeSel, Prbs0ChkModeSel
     *   - Dependencies:
     *     - None
     */
    //dwc_ddrphy_phyinit_io_write32(tPPGC  | csr_Prbs0GenModeSel_ADDR, 0x0002);
    dwc_ddrphy_phyinit_io_write32((c_addr | tDBYTE | csr_Prbs0ChkModeSel_ADDR), 0x0002);
  } // for byte

    /**
     * - Program Prbs0GenStateHi, Prbs0GenStateLo, Prbs0ChkStateHi, Prbs0ChkStateLo:
     *   - Description: Configure the PPGC pattern used for PPT2 RxClk and TxDQ
     *   - Fields:
     *     - Prbs0GenStateHi, Prbs0GenStateLo, Prbs0ChkStateHi, Prbs0ChkStateLo
     *   - Dependencies:
     *     - None
     */
    dwc_ddrphy_phyinit_io_write32(tPPGC  | csr_Prbs0GenStateHi_ADDR, 0x5a3c); // TX Gen pattern high
    dwc_ddrphy_phyinit_io_write32(tPPGC  | csr_Prbs0GenStateLo_ADDR, 0x5a3c); // TX Gen pattern low

    /**
     * - Program Prbs0GenModeSel, Prbs0ChkModeSel:
     *   - Description: Configure the PPGC to be pattern mode when used for PPT2 RxClk and TxDQ
     *   - Fields:
     *     - Prbs0GenModeSel, Prbs0ChkModeSel
     *   - Dependencies:
     *     - None
     */
    dwc_ddrphy_phyinit_io_write32(tPPGC  | csr_Prbs0GenModeSel_ADDR, 0x0002);
} // progPpt

/** \brief Programs PIE group disable flags.
 *
 * This is a helper function to program PIE Group Flag registers.It is called by dwc_ddrphy_phyinit_I_loloadPIEImage().
 *
 * \param phyctx   Data structure to hold user-defined parameters
 *
 * \param prog_csr Value of initCtrl[0] which controls if progCsrSkipTrain() function is called
 *
 * \return void
 *
 * Detailed list of registers programmed by this function:
 */
void dwc_ddrphy_phyinit_PieFlags(phyinit_config_t *phyctx, int prog_csr)
{
  uint16_t regData;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag0_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag1_ADDR), 0x00FE);
  if (prog_csr == 1 || (pUserInputAdvanced->DisableRetraining != 0)) {
    regData = 0xFFFF;
    dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag2_ADDR), regData);
  } else {
    regData = 0x00A8;
    dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag2_ADDR), regData);
  }
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag3_ADDR), 0xF040);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag4_ADDR), 0xF040);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag5_ADDR), 0x0000);
  
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag6_ADDR), 0xFFFF);
  
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag7_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag8_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag9_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag10_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag11_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag12_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag13_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag14_ADDR), 0x0000);
  dwc_ddrphy_phyinit_io_write32((tINITENG | csr_Seq0BDisableFlag15_ADDR), 0x0000);
} // End of dwc_ddrphy_phyinit_PieFlags

/** \brief Helper function to write MR instructions
 *
 * This is a helper function to program ACSM runtime instructions.
 *
 * \param mrNum  Which MR number to write to
 * \param mrVal  Data of the MR to write
 * \param mrCs   Drives the CS pins
 * \param dly    Command delay
 *
 * \return void
 *
 * Detailed list of registers programmed by this function:
 */
extern void dwc_ddrphy_mr_inst(uint8_t mrNum, uint8_t mrVal, uint8_t mrCs, uint16_t dly);
void dwc_ddrphy_mr_inst(uint8_t mrNum,  //!< Which MR number to write to
                        uint8_t mrVal,  //!< Data of the MR to write
                        uint8_t mrCs,  //!< drives the cs pins
                        uint16_t dly)  //!< Command delay
{

  dwc_ddrphy_phyinit_cmnt("[%s] Storing MRW MA=%d OP=0x%x CS=0x%x at row addr=0x%0x\n", __func__, mrNum, mrVal, mrCs, acsmInstPtr / 4);

  uint16_t addr[8] = { 0 };
  uint16_t cs[8] = { 0 };

  
    uint16_t p[4];

    p[0] = 0x58; // MRW-1
    p[1] = mrNum; // MA[6:0]
    p[2] = 0x8u | (mrVal & 0x80u) >> 1u; // MRW-2 + OP7
    p[3] = mrVal & 0x7Fu; // OP[6:0]
    addr[0] = (p[1] & 0x7Fu) << 7u | (p[0] & 0x7Fu);
    addr[1] = (p[3] & 0x7Fu) << 7u | (p[2] & 0x7Fu);
    cs[0] = mrCs & 0x3u;
    cs[1] = mrCs & 0x3u;

  

  //dwc_ddrphy_phyinit_cmnt(" [%s] test2\n", __func__);
  uint16_t acsm_addr = acsmInstPtr;
  uint16_t ac_instr[8] = { 0 };
  uint32_t acsm_addr_mask;
  uint32_t acsm_cs_mask;

  // Converting to 32-bit CSR addressing format
  if (acsmInstPtr & 0x1u){
    dwc_ddrphy_phyinit_assert(0,"acsmInstPtr is Odd: %d\n", acsmInstPtr);
  }
  acsm_addr = acsmInstPtr>>1;

  
    acsm_addr_mask = 0x3fff;
    acsm_cs_mask = 0x3;
    // even
    ac_instr[0] = ((cs[0] & acsm_cs_mask) << 14) | (addr[0] & acsm_addr_mask);
    ac_instr[1] = 0;
    ac_instr[2] = 0;
    ac_instr[3] = 0;
    // odd
    ac_instr[4] = ((cs[1] & acsm_cs_mask) << 14) | (addr[1] & acsm_addr_mask);
    ac_instr[5] = 0;
    ac_instr[6] = 0;
    ac_instr[7] = 0;

  

  

  //dwc_ddrphy_phyinit_cmnt(" [%s] test3\n", __func__);
  uint16_t x;

  for (x = 0; x < 4; x++) {
    //dwc_ddrphy_phyinit_cmnt(" [%s] addr=0x%x\n", __func__, acsm_addr);
    //dwc_ddrphy_phyinit_cmnt(" [%s] addr=0x%x\n", __func__, x);
    //dwc_ddrphy_phyinit_cmnt(" [%s] dat=0x%x\n", __func__, ac_instr[x]);
    dwc_ddrphy_phyinit_io_write32((acsm_addr | ACSM_START_CSR_ADDR) + x, ( (uint32_t) (ac_instr[2*x+1]) << 16) | ac_instr[2*x]);
  }

  acsmInstPtr += 8;

  uint32_t cnt = dly >> 1;
  dwc_ddrphy_phyinit_cmnt("[%s] dly = %d cnt = %d\n", __func__, dly, cnt);

  if (dly > 0) {
    for (x = 4; x < 8; x++) {
      if (x == 5 && dly > 2){
        dwc_ddrphy_phyinit_io_write32((acsm_addr | ACSM_START_CSR_ADDR) + x, ((cnt & 0x07u) << 12u | 0xb00u) << 16u);
      }
      else if (x == 7){
        dwc_ddrphy_phyinit_io_write32((acsm_addr | ACSM_START_CSR_ADDR) + x, ((cnt & 0xf8u) << 7u) << 16u);
      }
      else{
        dwc_ddrphy_phyinit_io_write32((acsm_addr | ACSM_START_CSR_ADDR) + x, 0);
      }
     }

     //dwc_ddrphy_phyinit_cmnt(" [%s] test6\n", __func__);
     acsmInstPtr += 8;
  }
}

/** \brief helper function to reserve space for MR instructions
 *
 * This is a helper function to manage ACSM instruction space.
 *
 * \return void
 *
 * Detailed list of registers programmed by this function:
 */
static void dwc_ddrphy_mr_clear(uint8_t mrNum, //!< MR number
                                uint8_t mrVal, //!< value ignored
                                uint8_t mrCs,  //!< value ignored
                                uint16_t dly)  //!< command delay, uses two additional acsm rows if != 0
{
  dwc_ddrphy_phyinit_cmnt("[%s] Reserving space for MRW MA=%d at row addr=0x%0x\n", __func__, mrNum, acsmInstPtr / 4);

  uint8_t rows = (dly == 0) ? 2 : 4;

  // Clear this section (write NOPs), write 2 32-bit pieces of data per row (i.e. rows*2)
  for (int x = 0; x < (rows*2); x++){
    dwc_ddrphy_phyinit_io_write32(((acsmInstPtr >> 1) | ACSM_START_CSR_ADDR) + x, 0x0);
  }

  // acsmInstPtr is still calculated in 16-bit chunks, so increment by rows*4
  acsmInstPtr += (rows * 4);
}

/** \brief helper function to skip over allocated space for MR instructions
 *
 * This is a helper function to manage ACSM instruction space.
 *
 * \return void
 *
 * Detailed list of registers programmed by this function:
 */
static void dwc_ddrphy_mr_skip(uint8_t mrNum, //!< MR number
                               uint8_t mrVal, //!< Value ignored
                               uint8_t mrCs, //!< Calue ignored
                               uint8_t dly, //!< Command delay, uses two additional acsm rows if != 0
                               uint8_t retEn) //!< Retention enable flag
{
  dwc_ddrphy_phyinit_cmnt("[%s] Skip over space for MRW MA=%d at row addr=0x%0x\n", __func__, mrNum, acsmInstPtr / 4);

  if (retEn == 0) {
    dwc_ddrphy_phyinit_cmnt("[%s] Skipping \n", __func__);
    // Skip over this section and rely on FW to program the MRW
    uint8_t rows = (dly == 0) ? 2 : 4;
    acsmInstPtr += (rows * 4);
  } else {
    uint16_t x;
    uint16_t acsm_addr = (acsmInstPtr>>1);

    for (x = 0; x < 4; x++) {
      dwc_ddrphy_phyinit_trackReg(((acsm_addr | ACSM_START_CSR_ADDR) + x));
      dwc_ddrphy_phyinit_cmnt("[%s] trackReg addr = %x\n", __func__, ((acsm_addr | ACSM_START_CSR_ADDR) + x));
    }
    acsmInstPtr += 8;

    if (dly > 0) {
      for (x = 4; x < 8; x++) {
        dwc_ddrphy_phyinit_trackReg((acsm_addr | ACSM_START_CSR_ADDR) + x);
        dwc_ddrphy_phyinit_cmnt("[%s] trackReg addr = %x\n", __func__, ((acsm_addr | ACSM_START_CSR_ADDR) + x));
      }

      acsmInstPtr += 8;
    }
  }
}

/** \brief helper function that abstracts the loading of MRW instructions
 *
 * This is a helper function to manage ACSM instruction space.
 *
 * \param mrNum  Which MR number to write to
 * \param mrVal  Data of the MR to write
 * \param mrCs   Drives the CS pins
 * \param dly    Command delay
 * \param skip   Nullify the function if set
 * \param retEn  Retention enabled flag
 *
 * \return void
 *
 * Detailed list of registers programmed by this function:
 */
extern void dwc_ddrphy_mr_load_cond(uint8_t mrNum, uint8_t mrVal, uint8_t mrCs, uint8_t dly, uint8_t skip, uint8_t retEn);
void dwc_ddrphy_mr_load_cond(uint8_t mrNum,  //!< Which MR number to write to
                             uint8_t mrVal, //!< Data of the MR to write
                             uint8_t mrCs, //!< Drives the cs pins
                             uint8_t dly, //!< Command delay
                             uint8_t skip, //!< Nullify the function, if set
                             uint8_t retEn) //!< Retention enable flag
{
  if (skip) {
    // Let firmware populate the MRW instruction, just skip over that section of memory
    return dwc_ddrphy_mr_skip(mrNum, mrVal, mrCs, dly, retEn);
  } else {
    return dwc_ddrphy_mr_inst(mrNum, mrVal, mrCs, dly);
  }
}

/** \brief Programs required initialization registers after trianing firmware execution.
 */
// coverity[misra_c_2012_rule_5_1_violation]
void dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(phyinit_config_t *phyctx)
{
  
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  uint32_t pstate = pRuntimeConfig->curPState;
  uint16_t regData;
  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s(), PState=%d\n", __func__, __func__, pstate);

  uint8_t skip_pie = (pRuntimeConfig->initCtrl & 0x10u) >> 4;
  if (skip_pie) {
    dwc_ddrphy_phyinit_cmnt("[%s] skip_pie flag set. Skipping dwc_ddrphy_phyinit_I_loadPIEImagePsLoop\n", __func__);
    return;
  }

  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  uint8_t devinit = (pRuntimeConfig->initCtrl & 0x20u) >> 5;
  uint8_t NumAchnActive = pRuntimeConfig->NumAchnActive;
  
  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive;
  uint32_t p_addr = pstate << 20;
  
  // Enable DFI channels based on userInput
  dwc_ddrphy_phyinit_programDfiMode(phyctx, enableDfiMode);
  /**
   * - Program ZCalReset, ZCalRun:
   *   - Description: Prepare the calibration controller for mission mode, turn on calibration and hold idel until dfi_init_start is asserted
   *   - Dependencies:
   *     - None
   */
  if( pstate == pUserInputBasic->FirstPState) {
    regData = 0x1;
    dwc_ddrphy_phyinit_cmnt("[%s] Turn on calibration and hold idle until dfi_init_start is asserted sequence is triggered.\n", __func__);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalReset to 0x%x\n", __func__, regData);
    dwc_ddrphy_phyinit_cmnt("[%s] Programming ZCalRun to 0x%x\n", __func__, regData);
    // Note: S3 waiver
    //       Purposely using userCustom_io_write32(), do not want to save ZCalReset to S3 list as if this
    //       CSR restored prior to HMZCAL CSR, HMZCAL will not be restored. 
    //       This CSR will be restored at the end of restore sequence 
    //       dwc_ddrphy_phyinit_restore_sequence.c
    dwc_ddrphy_phyinit_userCustom_io_write32((tZCAL | csr_ZCalReset_ADDR), regData);
    dwc_ddrphy_phyinit_io_write32((tZCAL | csr_ZCalRun_ADDR), regData);
  }




  // Program PLL (PllCtrl5 and PllCtrl6) for mission mode (fast relock)
  dwc_ddrphy_phyinit_programPLL(phyctx, 1, "[phyinit_I_loadPIEImagePsLoop]");

  //csrCPllForceCal [9:9]= 1 and csrCPllEnCal [10:10] = 0	
  dwc_ddrphy_phyinit_io_write32((tHMMAS | csr_CPllCtrl3_ADDR),0x3f0); 


 
  // Program SingleEndedMode based on user input
  uint16_t semCK = 0;
  uint16_t semWDQS = 0;
  uint16_t semWCK = 0;

  // Set the singleEndedMode variable based off the Mode Register input.
  uint16_t singleEndedModeCK;
  uint16_t singleEndedModeWCK;
  singleEndedModeCK = (mb1D[pstate].MR1_A0 & 0x8u) >> 3;
  singleEndedModeWCK = (mb1D[pstate].MR20_A0 & 0xcu) >> 2;

  switch (singleEndedModeCK) {
  case 0:
    break;
  case 1:
    semCK = 1;
    break;
  default:
    dwc_ddrphy_phyinit_assert(0, "[%s] Invalid singleEndedModeCK = %d, pstate = %d\n", __func__, singleEndedModeCK, pstate);
    break;
  }
  switch (singleEndedModeWCK) {
  case 0:
    break;
  case 1:
    semWCK = 1;
    break;
  case 2:
    semWCK = 2;
    break;
  default:
    dwc_ddrphy_phyinit_assert(0, "[%s] Invalid singleEndedModeWCK = %d, pstate = %d\n", __func__, singleEndedModeWCK, pstate);
    break;
  }


  /**
   * - Program SingleEndedMode:
   *   - Description: Program control for single ended mode
   *   - Fields:
   *     - SingleEndedWCK
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumCh
   *     - user_input_basic.NumDbytesPerCh
   *     - mb1D[ps].MR51_A0[3:3] (LPDDR4)
   *     - mb1D[ps].MR51_A0[2:2] (LPDDR4)
   *     - mb1D[ps].MR1_A0[3:3]  (LPDDR5)
   *     - mb1D[ps].MR20_A0[3:2] (LPDDR5)
   */
  uint16_t ACsingleEndedMode = ((semCK << csr_SingleEndedCK_LSB) & csr_SingleEndedCK_MASK);

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming SingleEndedMode::SingleEndedCK to 0x%x\n", __func__, pstate, semCK);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming SingleEndedMode to 0x%x\n", __func__, pstate, ACsingleEndedMode);
  for (unsigned achn = 0; achn < NumAchnActive; achn++) {
    unsigned c_addr = achn << 12;
    dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | csr_ACSingleEndedMode_ADDR), ACsingleEndedMode);
  }
  uint16_t singleEndedMode = ((semWDQS << csr_SingleEndedDQS_LSB) & csr_SingleEndedDQS_MASK)
                | ((semWCK << csr_SingleEndedWCK_LSB) & csr_SingleEndedWCK_MASK);

  for (unsigned byte=0; byte<NumDbyteActive; byte++) {
    unsigned c_addr = byte << 12;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming SingleEndedMode::SingleEndedDQS to 0x%x\n", __func__, pstate, semWDQS);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming SingleEndedMode::SingleEndedWCK to 0x%x\n", __func__, pstate, semWCK);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming SingleEndedMode to 0x%x\n", __func__, pstate, singleEndedMode);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_SingleEndedMode_ADDR), singleEndedMode);
  }

  if (devinit) {
    //Training Firmware requires all clocks/strobes to be in differential mode
    for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
      unsigned c_addr = byte << 12;
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_SingleEndedMode_ADDR), 0);
    }
    for (unsigned achn = 0; achn < NumAchnActive; achn++) {
      unsigned c_addr = achn << 12;
      dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | csr_ACSingleEndedMode_ADDR), 0);
    }
  }

  /**
   * - Program ACSMWckFreeRunMode:
   *   - Description: Extends WCK pulses in free running mode
   *   - Dependencies:
   *     - mb1D[ps].MR18_A0[4:4]
   */
  regData = (((mb1D[pstate].MR18_A0 & 0x10u) >> 4u) == 1u)? 0x1 : 0x0;
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming ACSMWckFreeRunMode to 0x%x\n", __func__, pstate, regData);
  dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckFreeRunMode_ADDR), regData);



  /**
   * - Program ZcalClkDiv:
   *   - Description: Program clock divider to ZCAL
   *   - Dependencies:
   *     - user_input_basic.ZcalClkDiv
   */
  if(pstate == pUserInputBasic->FirstPState) {
     dwc_ddrphy_phyinit_cmnt("[%s] Programming ZcalClkDiv to 0x%x\n", __func__, pUserInputAdvanced->ZcalClkDiv[pUserInputBasic->FirstPState]);
     // Note: S3 waiver
     //       Purposely using userCustom_io_write32(), do not want to save ZcalClkDiv to S3 list as if this
     //       CSR restored prior to HMZCAL CSR, HMZCAL will not be restored. 
     //       This CSR will be restored at the end of restore sequence 
     //       dwc_ddrphy_phyinit_restore_sequence.c
     dwc_ddrphy_phyinit_userCustom_io_write32 ((tZCAL | csr_ZcalClkDiv_ADDR),pUserInputAdvanced->ZcalClkDiv[pUserInputBasic->FirstPState]);

  }



  /**
   * - Program GPR12:
   *   - Description: Program ZcalClkDiv value in GPR12 for PIE to use
   *   - Dependencies:
   *     - user_input_basic.ZcalClkDiv
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming GPR12 with Zcalkclkdiv to 0x%x\n", __func__, pstate, pUserInputAdvanced->ZcalClkDiv[pstate]);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BGPR12_ADDR),pUserInputAdvanced->ZcalClkDiv[pstate]);

  /**
   * - Program RxClkCnt1:
   *   - Description: Enable RxReplica after FW training has executed
   *   - Fields:
   *     - EnRxClkCor
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumDbytesPerCh
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.Frequency
   *     - user_input_advanced.DisableRetraining
   *     - user_input_advanced.RxClkTrackEn
   *     - mb1D[ps].MR20_A0[1:0] (LPDDR5)
   */
  uint16_t RxReplicaTrackEn = (pUserInputAdvanced->RxClkTrackEn[pstate] == 1) ? 1 : 0;
  int DisableRetraining = pUserInputAdvanced->DisableRetraining;

  int rxClkThreshold;
  uint32_t frequencyPstate = pUserInputBasic->Frequency[pstate];

    rxClkThreshold = pUserInputBasic->DfiFreqRatio[pstate] == 1 ? 400 : 200;

  if (frequencyPstate < rxClkThreshold && RxReplicaTrackEn == 1){
    dwc_ddrphy_phyinit_assert(0, " [%s] Pstate=%d RxClk tracking cannot be enabled for low data rates, CK frequency = %d\n", __func__, pstate, pUserInputBasic->Frequency[pstate]);
  }

  if (DisableRetraining != 0 && RxReplicaTrackEn == 1){
    dwc_ddrphy_phyinit_assert(0, " [%s] Pstate=%d RxClk tracking cannot be enabled when retraining is disabled (DisableRetraining = %d)\n", __func__, pstate, DisableRetraining);
  }

  if ((mb1D[pstate].MR20_A0 & 0x3u) == 0x0u && RxReplicaTrackEn == 1){
    dwc_ddrphy_phyinit_assert(0, " [%s] Pstate=%d RxClk tracking cannot be enabled in strobe-less read mode\n", __func__, pstate);
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming RxClkCntl1 to 0x%x\n", __func__, pstate, RxReplicaTrackEn);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = c1 * byte;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxClkCntl1_ADDR), RxReplicaTrackEn);
  }

  /**
   * - Program RxReplicaCtl04:
   *   - Description: Program RxReplica controls
   *   - Fields:
   *     - RxReplicaTrackEn
   *     - RxReplicaLongCal
   *     - RxReplicaStride
   *     - RxReplicaPDenFSM
   *     - RxReplicaPDRecoverytime
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.NumDbytesPerCh
   */
  uint16_t RxReplicaCtl;
  
    RxReplicaCtl =  (RxReplicaTrackEn << csr_RxReplicaTrackEn_LSB)
                         | (0u << csr_RxReplicaLongCal_LSB)                       // switch to short cal during mission mode
                         | (2u << csr_RxReplicaStride_LSB)                        // Keep the default value of 1 step
                         | (0u << csr_RxReplicaPDenFSM_LSB);                      // FSM driven RxReplica Receiver Powerdown is not needed due to HM port RxReplica_RxPowerDown_DQS removed.
  
  
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming RxReplicaCtl04 to 0x%x\n", __func__, pstate, RxReplicaCtl);

  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr = c1 * byte;
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr | tDBYTE | csr_RxReplicaCtl04_ADDR), RxReplicaCtl);
  }

  /**
   * - Program TxDcaMode:
   *   - Description: Program DCD control enables for DQ/DQS
   *   - Dependencies:
   *     - usre_input_basic.DramType
   *     - user_input_basic.Frequency
   *     - user_input_basic.DfiFreqRatio
   *     - user_input_basic.NumDbytesPerCh
   */
  // Program TxDcaMode (TxDQDcaMode/TxDiffDcaMode) for WCK after training was done (LPDDR5)
  uint16_t txDcaMode = 0;
  // enable WCK DCA mode when WCK is in the higher range, above 2.5GHz
  uint32_t dfiFreqRatio = pUserInputBasic->DfiFreqRatio[pstate];
  if (frequencyPstate << dfiFreqRatio >= 2500) {
    txDcaMode = 1;
  }
  // for each chiplet
  for (int byte = 0; byte < NumDbyteActive; byte++) {
    uint32_t c_addr0 = (byte*2) * c1;
    uint32_t c_addr1 = ((byte*2)+1) * c1;
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr0 | tHMDBYTE | csr_TxDQDcaMode_ADDR), txDcaMode);
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr0 | tHMDBYTE | csr_TxDiffDcaMode_ADDR), txDcaMode);
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr1 | tHMDBYTE | csr_TxDQDcaMode_ADDR), txDcaMode);
    dwc_ddrphy_phyinit_io_write32((p_addr | c_addr1 | tHMDBYTE | csr_TxDiffDcaMode_ADDR), txDcaMode);
  }

  /**
   * - Program RtrnMode:
   *   - Description: Program select for for PPT2
   *   - Dependencies:
   *     - user_input_advanced.RetrainMode
   */
  regData = (pUserInputAdvanced->RetrainMode[pstate] == 4) ? 0x1 : 0x0;
  dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming RtrnMode to 0x%x\n", __func__, pstate, regData);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_RtrnMode_ADDR), regData);

  /**
   * - Program Seq0BGPR18:
   *   - Description: Save DtsmByteCtrl0[Dtsm8bitMode] for PIE PPT2
   *   - Dependencies:
   *     - user_input_advanced.RetrainMode
   */
  if (pUserInputAdvanced->RetrainMode[pstate] == 4) {
    regData = (pUserInputBasic->DfiFreqRatio[pstate] == 1) ? 0x0 : csr_Dtsm8bitMode_MASK;
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming Seq0BGPR18 to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BGPR18_ADDR), regData);
  }

  /**
   * - Program Seq0BGPR19:
   *   - Description: Save PrbsGenCtrl[PpgcGen8bitMode] for PIE PPT2
   *   - Dependencies:
   *     - user_input_advanced.RetrainMode
   */
  if (pUserInputAdvanced->RetrainMode[pstate] == 4) {
    regData = (pUserInputBasic->DfiFreqRatio[pstate] == 1) ? 0x0 : csr_PpgcGen8bitMode_MASK;
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming Seq0BGPR19 to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BGPR19_ADDR), regData);
  }

  /**
   * - Program Seq0BCntr{0,1,2}Threshold:
   *   - Description: Set the thresholds for the PPT2 sequence generation
   *   - Dependencies:
   *     - user_input_advanced.RetrainMode
   *     - user_input_basic.DramType
   *     - user_input_basic.NumRank_dfi0
   *     - user_input_basic.NumActiveDbyteDfi1
   *     - mb1D[ps].MR22[WECC]
   */
  if (pUserInputAdvanced->RetrainMode[pstate] == 4) {
    // Seq0BCntr0Threshold controls sequence type (RxClk, RxEn, TxDq1, TxDq2), but TxDq2 is only for LP5+WECC
    uint16_t writeLinkEcc = (mb1D[pstate].MR22_A0 >> 4) & 0x3u;
    regData = (writeLinkEcc == 0x1) ? 0x3 : 0x2;
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming Seq0BCntr0Threshold to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BCntr0Threshold_ADDR), regData);

    // Seq0BCntr1Threshold controls number of ranks
    regData = (pUserInputBasic->NumRank_dfi0 == 1) ? 0x0 : 0x1;
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming Seq0BCntr1Threshold to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BCntr1Threshold_ADDR), regData);

    // Seq0BCntr2Threshold controls number of channels
    regData = (pUserInputBasic->NumActiveDbyteDfi1 == 0) ? 0x0 : 0x1;
    dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Programming Seq0BCntr2Threshold to 0x%x\n", __func__, pstate, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BCntr2Threshold_ADDR), regData);
  }

  /**
   * - Program HwtLpCsEnA, HwtLpCsEnB, Seq0BGPR14, Seq0BGPR15:
   *   - Description: Program CSn disable for channel A/B, save values of HwtLpCsEn{A,B} in GPR14/15 for PIE to use
   *   - Dependencies:
   *     - user_input_basic.DramType
   *     - user_input_basic.NumRank_dfi0
   *     - user_input_basic.NumRank_dfi1
   *     - usre_input_basic.NumCh
   */
  uint16_t HwtLpCsEnA;
  uint16_t HwtLpCsEnB;
  uint16_t numActiveRanks = 0x1;

  // Channel A - 1'b01 if signal-rank, 2'b11 if dual-rank
  uint32_t numRankDfi0 = pUserInputBasic->NumRank_dfi0;
  uint32_t numRankDfi1 = pUserInputBasic->NumRank_dfi1;
  HwtLpCsEnA = numRankDfi0 | numActiveRanks;

  // Channel B - 1'b01 if signal-rank, 2'b11 if dual-rank
  // if DFI1 exists but disabled, NumRank_dfi0 is used to program CsEnB
  if (pUserInputBasic->NumCh == 2 && pUserInputBasic->NumActiveDbyteDfi1 == 0) {
    HwtLpCsEnB = numRankDfi0 | numActiveRanks;
  } else if (pUserInputBasic->NumCh == 2 && pUserInputBasic->NumActiveDbyteDfi1 > 0) {
    HwtLpCsEnB = numRankDfi1 | numActiveRanks;
  } else { // Disable Channel B
    HwtLpCsEnB = 0x0;
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Programming HwtLpCsEnA to 0x%x\n", __func__, HwtLpCsEnA);
  dwc_ddrphy_phyinit_io_write32((tPPGC | csr_HwtLpCsEnA_ADDR), HwtLpCsEnA);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR14_ADDR),HwtLpCsEnA);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming HwtLpCsEnB to 0x%x\n", __func__, HwtLpCsEnB);
  dwc_ddrphy_phyinit_io_write32((tPPGC | csr_HwtLpCsEnB_ADDR), HwtLpCsEnB);
  dwc_ddrphy_phyinit_io_write32((p_addr | c0 | tINITENG | csr_Seq0BGPR15_ADDR),HwtLpCsEnB);


    if (pUserInputAdvanced->RetrainMode[pstate] == 0x4) {
      /**
       * - Program ACSMWckWriteFastTogglePulse:
       *   - Description: Step C may have adjusted WckWriteFastToggle values for PPT2, apply here after Training FW is complete
       *   - Dependencies:
       *     - user_input_basic.DramType
       *     - user_input_basic.DfiFreqRatio
       *     - user_input_advanced.RetrainMode
       */
      uint16_t wrFTGdly = phyctx->wrFTGdly[pstate];
      uint16_t wrFTGwd  = phyctx->wrFTGwd[pstate];
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, PPT2 programming ACSMWckWriteFastToggleWidth to 0x%x, ACSMWckWriteFastToggleDelay to 0x%x\n", __func__, pstate, wrFTGwd, wrFTGdly);
      dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMWckWriteFastTogglePulse_ADDR), (wrFTGwd << csr_ACSMWckWriteFastToggleWidth_LSB) | (wrFTGdly << csr_ACSMWckWriteFastToggleDelay_LSB));
    }

  dwc_ddrphy_phyinit_cmnt("[%s] End of %s(), PState=%d\n", __func__, __func__, pstate);

} // End of  dwc_ddrphy_phyinit_I_loadPIEImagePsLoop (phyinit_config_t *phyctx)


/** \brief Program the sequence of MRW instructions in the ACSM memory
 *
 * This is a helper function to manage ACSM instruction space.
 *
 * \param phyctx    Data structure to hold user-defined parameters.
 * \param inPsLoop  Flag to indicate if the function is called during the
 *                  PState loop sequence.
 *
 * \return The MRW dly that was used to space out the MRW.
 *
 */

static void loadAcsmMRW(phyinit_config_t *phyctx, int inPsLoop) {
  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s() inPsLoop=%d\n", __func__, __func__, inPsLoop);

  /// - Program ACSM runtime MRW instructions.
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;

  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  uint8_t cs = (pUserInputBasic->NumRank == 2) ? 0xf : 0x5; // for 2CK commands
  uint8_t tg0 = 0x5;
  uint8_t tg1 = (pUserInputBasic->NumRank == 2) ? 0xa : 0x0;
  uint8_t prog_csr = (pRuntimeConfig->initCtrl & 0x1u) >> 0;
  uint8_t skipMr = (prog_csr == 0) ? 1 : 0;
  uint8_t firstPs = pUserInputBasic->FirstPState;
  uint8_t retEn = pRuntimeConfig->RetEn;
  uint16_t tck_ps;
  uint8_t dly;
  uint16_t cfgPstates = pUserInputBasic->CfgPStates;

  uint16_t acsmMRPtrs[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE][2] = {
    {mb1D[firstPs].FCDfi0AcsmStartPS0, mb1D[firstPs].FCDfi1AcsmStartPS0},
    {mb1D[firstPs].FCDfi0AcsmStartPS1, mb1D[firstPs].FCDfi1AcsmStartPS1},
    {mb1D[firstPs].FCDfi0AcsmStartPS2, mb1D[firstPs].FCDfi1AcsmStartPS2},
    {mb1D[firstPs].FCDfi0AcsmStartPS3, mb1D[firstPs].FCDfi1AcsmStartPS3}
  };

  for (uint16_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {





      uint32_t p_addr = (uint32_t) pstate << 20;


      uint16_t start = acsmInstPtr / 4 ;
      uint16_t startSectionA, startSectionB;
      tck_ps = pRuntimeConfig->tck_ps[pstate];
      dly = ((5*tck_ps) > 10000.0) ? 5 : (int)ceil(10000.0/tck_ps); // tMRWmin is max(10ns, 5nCK)
      dwc_ddrphy_phyinit_cmnt("[%s] PState=%d, Frequency=%d, tck_ps=%d, dly=%d\n", __func__, pstate, pUserInputBasic->Frequency[pstate], tck_ps, dly);
      // Skipping programming unused PState CSR
      if (cfgPstates & 0x1u) {
        dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming ACSMRptCntOverride to %d\n", __func__, pstate, (int)ceil(dly/2.0)-2);
        dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_ACSMRptCntOverride_ADDR), (int)ceil(dly/2.0)-2);
      }
      cfgPstates = cfgPstates >> 1;

      if (dly > 100){
        dwc_ddrphy_phyinit_assert(0, " [%s] Unexpected dly value. dly=%d\n", __func__, dly);
      }

      uint8_t vbsMask[4];

    
      // For X16 devices, send MR12 twice.
      // For X8  devices, send MR12 for VBS = 0 and 1
      for (uint32_t rank = 0; rank < 4; rank++) {
        vbsMask[rank] = ((mb1D[pstate].X8Mode & (1u << rank)) == 1) ? 0x80u : 0x00u;
      }

      dwc_ddrphy_phyinit_cmnt("[%s] MR1=0x%x\n", __func__, mb1D[pstate].MR1_A0);
      dwc_ddrphy_mr_inst(19, mb1D[pstate].MR19_A0,  cs, dly); // 
      dwc_ddrphy_mr_inst(18, mb1D[pstate].MR18_A0,  cs, dly);
      dwc_ddrphy_mr_inst(1,  mb1D[pstate].MR1_A0,   cs, dly);
      dwc_ddrphy_mr_inst(2,  mb1D[pstate].MR2_A0,   cs, dly);
      dwc_ddrphy_mr_inst(3,  mb1D[pstate].MR3_A0,   cs, dly);
      dwc_ddrphy_mr_inst(10, mb1D[pstate].MR10_A0,  cs, dly);
      dwc_ddrphy_mr_inst(11, mb1D[pstate].MR11_A0,  cs, dly);
      dwc_ddrphy_mr_inst(17, mb1D[pstate].MR17_A0, tg0,   0); // MR17_A0 for MR17_B0 as well
      dwc_ddrphy_mr_inst(17, mb1D[pstate].MR17_A1, tg1, dly); // MR17_A1 for MR17_B1 as well
      dwc_ddrphy_mr_inst(20, mb1D[pstate].MR20_A0,  cs, dly);
      dwc_ddrphy_mr_inst(22, mb1D[pstate].MR22_A0,  cs, dly);
      dwc_ddrphy_mr_inst(41, mb1D[pstate].MR41_A0,  cs, dly);
      if (pUserInputBasic->Lp5xMode == 1) {
        dwc_ddrphy_mr_inst(58, mb1D[pstate].MR58_A0,  cs,   0);
      } else {
        dwc_ddrphy_mr_clear(58, mb1D[pstate].MR58_A0, cs,  0);
      }

      startSectionA = (acsmInstPtr / 4);

      // Trained Mode Registers: per rank, per channel
      // Channel A
      dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_A0 & (~vbsMask[0]), tg0,   0, skipMr, retEn); // Vref CA (lower byte for x8)
      dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_A1 & (~vbsMask[1]), tg1, dly, skipMr, retEn);
      dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_A0 | ( vbsMask[0]), tg0,   0, skipMr, retEn); // Vref CA upper byte for x8 (use same value for lower/upper in skipTrain)
      dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_A1 | ( vbsMask[1]), tg1, dly, skipMr, retEn);
      dwc_ddrphy_mr_load_cond(14, mb1D[pstate].MR14_A0, tg0,   0, skipMr, retEn); // Vref DQ [7:0]
      dwc_ddrphy_mr_load_cond(14, mb1D[pstate].MR14_A1, tg1, dly, skipMr, retEn);
      dwc_ddrphy_mr_load_cond(15, mb1D[pstate].MR15_A0, tg0,   0, skipMr, retEn); // Vref DQ [15:8]
      dwc_ddrphy_mr_load_cond(15, mb1D[pstate].MR15_A1, tg1, dly, skipMr, retEn);
      dwc_ddrphy_mr_load_cond(24, mb1D[pstate].MR24_A0, tg0,   0, skipMr, retEn); // DFE DBYTE
      dwc_ddrphy_mr_load_cond(24, mb1D[pstate].MR24_A1, tg1, dly, skipMr, retEn);
      dwc_ddrphy_mr_load_cond(30, mb1D[pstate].MR30_A0, tg0,   0, skipMr, retEn); // WCK DCA
      dwc_ddrphy_mr_load_cond(30, mb1D[pstate].MR30_A1, tg1, dly, skipMr, retEn);
      if (pUserInputBasic->Lp5xMode == 1) {
        dwc_ddrphy_mr_load_cond(69, mb1D[pstate].MR69_A0, tg0,   0, skipMr, retEn); // Read DCA
        dwc_ddrphy_mr_load_cond(69, mb1D[pstate].MR69_A1, tg1, dly, skipMr, retEn);
      } else {
        dwc_ddrphy_mr_clear(69, mb1D[pstate].MR69_A0, tg0,   0); // Read DCA
        dwc_ddrphy_mr_clear(69, mb1D[pstate].MR69_A1, tg1, dly);
      }
      startSectionB = (acsmInstPtr / 4);

      // Channel B
      if (pUserInputBasic->NumCh == 2 && pUserInputBasic->NumActiveDbyteDfi1 != 0) {
        dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_B0 & (~vbsMask[2]), tg0,   0, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_B1 & (~vbsMask[3]), tg1, dly, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_B0 | ( vbsMask[2]), tg0,   0, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(12, mb1D[pstate].MR12_B1 | ( vbsMask[3]), tg1, dly, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(14, mb1D[pstate].MR14_B0, tg0,   0, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(14, mb1D[pstate].MR14_B1, tg1, dly, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(15, mb1D[pstate].MR15_B0, tg0,   0, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(15, mb1D[pstate].MR15_B1, tg1, dly, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(24, mb1D[pstate].MR24_B0, tg0,   0, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(24, mb1D[pstate].MR24_B1, tg1, dly, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(30, mb1D[pstate].MR30_B0, tg0,   0, skipMr, retEn);
        dwc_ddrphy_mr_load_cond(30, mb1D[pstate].MR30_B1, tg1, dly, skipMr, retEn);
        if (pUserInputBasic->Lp5xMode == 1) {
          dwc_ddrphy_mr_load_cond(69, mb1D[pstate].MR69_B0, tg0,   0, skipMr, retEn);
          dwc_ddrphy_mr_load_cond(69, mb1D[pstate].MR69_B1, tg1, dly, skipMr, retEn);
        } else {
          dwc_ddrphy_mr_clear(69, mb1D[pstate].MR69_B0, tg0,   0);
          dwc_ddrphy_mr_clear(69, mb1D[pstate].MR69_B1, tg1, dly);
        }
      } else {
        dwc_ddrphy_mr_clear(12, mb1D[pstate].MR12_B0 & (~vbsMask[2]), tg0,   0);
        dwc_ddrphy_mr_clear(12, mb1D[pstate].MR12_B1 & (~vbsMask[3]), tg1, dly);
        dwc_ddrphy_mr_clear(12, mb1D[pstate].MR12_B0 | ( vbsMask[2]), tg0,   0);
        dwc_ddrphy_mr_clear(12, mb1D[pstate].MR12_B1 | ( vbsMask[3]), tg1, dly);
        dwc_ddrphy_mr_clear(14, mb1D[pstate].MR14_B0, tg0,   0);
        dwc_ddrphy_mr_clear(14, mb1D[pstate].MR14_B1, tg1, dly);
        dwc_ddrphy_mr_clear(15, mb1D[pstate].MR15_B0, tg0,   0);
        dwc_ddrphy_mr_clear(15, mb1D[pstate].MR15_B1, tg1, dly);
        dwc_ddrphy_mr_clear(24, mb1D[pstate].MR24_B0, tg0,   0);
        dwc_ddrphy_mr_clear(24, mb1D[pstate].MR24_B1, tg1, dly);
        dwc_ddrphy_mr_clear(30, mb1D[pstate].MR30_B0, tg0,   0);
        dwc_ddrphy_mr_clear(30, mb1D[pstate].MR30_B1, tg1, dly);
        dwc_ddrphy_mr_clear(69, mb1D[pstate].MR69_B0, tg0,   0);
        dwc_ddrphy_mr_clear(69, mb1D[pstate].MR69_B1, tg1, dly);
      }
    

      uint16_t stop = (acsmInstPtr / 4) - 1; // acsmInstPtr tracks current position
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Using MRW start address 0x%x.\n", __func__, pstate, start);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Using MRW Ch A address 0x%x.\n", __func__, pstate, startSectionA);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Using MRW Ch B address 0x%x.\n", __func__, pstate, startSectionB);
      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d Using MRW stop address 0x%x.\n", __func__, pstate, stop);

      // Check ACSM message block field values that were passed down to firmware earlier
      if (acsmMRPtrs[pstate][0] != startSectionA) {
        dwc_ddrphy_phyinit_assert(0, " [%s] Pstate=%d Mismatch for FCDfi0AcsmStartPS%d 0x%x vs ACSM Ch0 addr 0x%x\n",
                __func__, pstate, pstate, acsmMRPtrs[pstate][0], startSectionA);
      }

      if (acsmMRPtrs[pstate][1] != startSectionB) {
        dwc_ddrphy_phyinit_assert(0, " [%s] Pstate=%d Mismatch for FCDfi1AcsmStartPS%d 0x%x vs ACSM Ch1 addr 0x%x\n",
                __func__, pstate, pstate, acsmMRPtrs[pstate][1], startSectionB);
      }

  }  // pstate loop

  dwc_ddrphy_phyinit_cmnt("[%s] End of %s() inPsLoop=%d\n", __func__, __func__, inPsLoop);
} // End of loadAcsmMRW

/** \brief Program the DLEP SystemECC sequence of MRW instructions in the ACSM memory
 *
 * This is a helper function to manage ACSM instruction space for DLEP SystemEcc.
 *
 * \param phyctx    Data structure to hold user-defined parameters.
 *
 */

/** @} */
/** \brief Tests that the given enable bits are set in the phyctx
 *
 * This function allows the PHY Initialization Engine (PIE) and ACSM
 * instructions and the associated registers to be programmed conditionally.
 *
 * \param phyctx      Data structure to hold user-defined parameters
 * \param enable_bits Bitmap to test against the contents of phyctx
 * \param mode        Comparison mode
 * \param type        Type of enable bits field to use
 *
 * \return int - 1 if enable_bits are set in phyctx
 */
int dwc_ddrphy_phyinit_TestPIEProdEnableBits(phyinit_config_t* phyctx, uint32_t enable_bits,
                                             uint32_t disable_bits, int mode, uint8_t type) {

    uint32_t phyctx_enable_bits = phyctx->runtimeConfig.enableBits[type];
    uint32_t tested_bits = phyctx_enable_bits & enable_bits;
    int test_value = 0;

    switch (mode) {
    case ENABLE_BITS_ANY_BITS:
        test_value = (tested_bits != 0u) ? 1 : 0;
        break;
    case ENABLE_BITS_NO_BITS:
        test_value = (tested_bits == 0u) ? 1 : 0;
        break;
    case ENABLE_BITS_ALL_BITS:
    case ENABLE_BITS_AND_DISABLE_BITS:
        test_value = ((tested_bits == enable_bits) &&
                ((phyctx_enable_bits & disable_bits) == 0)) ? 1 : 0;
        break;
    default:
        test_value = 0;
        break;
   }
   return test_value;
}
/** @} */

/** \brief Converts a global address to a offset
 *
 * \param fixup_value Global address to use as a fixup
 *
 * \return - Offset, in words, from start of SRAM memory
 */
uint32_t dwc_ddrphy_phyinit_ConvertFixupSramAddress(uint32_t fixup_value) {
    if (fixup_value >= PIE_START_CSR_ADDR) {
        fixup_value -= PIE_START_CSR_ADDR;
        fixup_value <<= 9u;
    } else {
        fixup_value -= ACSM_START_CSR_ADDR;
        fixup_value >>= 2u;
    }
    return fixup_value;
}

/** \brief Generates calls to ...io_write..
 *
 * This function translates the code section and code data (word) arrays
 * into calls to ...io_write... that create the PIE and ACSM images.
 *
 * This function also fills in code markers with the start address of each
 * given code section.
 *
 * \param phyctx        Data structure to hold user-defined parameters
 * \param code_sections Array of structures for continuous address sections of code
 * \param code_section_count Size of the code_sections array
 * \param code_data     Array of words that make up data for the code sections
 * \param code_data_count Size of the code_data array
 * \param code_markers  Array of code_markers, sorted by code index
 * \param code_marker_count Size of the code_markers array
 *
 */
void dwc_ddrphy_phyinit_LoadPIECodeSections(phyinit_config_t* phyctx,
        code_section_t* code_sections, size_t code_section_count,
        uint32_t* code_data, size_t code_data_count,
        code_marker_t* code_markers, size_t code_marker_count) {
    dwc_ddrphy_phyinit_cmnt ("[%s] Start of %s()\n", __func__, __func__);
    user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
    for (size_t pass_num = 0; pass_num < 2; ++pass_num) {
        code_section_t* current_code_section = code_sections;
        uint32_t current_address = 0;
        size_t marker_index = 0;
        size_t data_index = 0;
        for (size_t section_index = 0; section_index < code_section_count; ++section_index) {
            // Handle conditional and start address (jump) sections
            uint8_t section_type = current_code_section->section_type;
            uint16_t section_len = current_code_section->section_len;
            uint8_t write_section = 1;
            switch (section_type) {
                case NORMAL_SECTION:
                    break;
                case START_ADDRESS:
                    if (pass_num == 1) {
                        dwc_ddrphy_phyinit_cmnt ("[%s] Moving start address from 0x%x to 0x%x\n", __func__,
                                current_address, current_code_section->start_address);
                    }
                    current_address = current_code_section->start_address;
                    break;
                case ENABLE_BITS_ANY_BITS:
                    {
                        if ((dwc_ddrphy_phyinit_TestPIEProdEnableBits(phyctx, current_code_section->enable_bits,
                                        0, ENABLE_BITS_ANY_BITS, current_code_section->enable_type)) == 0) {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] No match for ANY enable_bits = 0x%x, type = 0x%x, section size = %u\n", __func__,
                                        current_code_section->enable_bits, current_code_section->enable_type, section_len);
                            }
                            write_section = 0;
                        } else {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] Matched ANY enable_bits = 0x%x, type = 0x%x\n", __func__,
                                        current_code_section->enable_bits, current_code_section->enable_type);
                            }
                        }
                        break;
                    }
                case ENABLE_BITS_NO_BITS:
                    {
                        if ((dwc_ddrphy_phyinit_TestPIEProdEnableBits(phyctx, current_code_section->enable_bits,
                                        0, ENABLE_BITS_NO_BITS,  current_code_section->enable_type)) == 0) {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] No match for NO enable_bits = 0x%x, type = 0x%x, section size = %u\n", __func__,
                                        current_code_section->enable_bits, current_code_section->enable_type, section_len);
                            }
                            write_section = 0;
                        } else {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] Matched NO enable_bits = 0x%x, type = 0x%x\n", __func__,
                                        current_code_section->enable_bits, current_code_section->enable_type);
                            }
                        }
                        break;
                    }
                case ENABLE_BITS_ALL_BITS:
                    {
                        if ((dwc_ddrphy_phyinit_TestPIEProdEnableBits(phyctx, current_code_section->enable_bits,
                                        0, ENABLE_BITS_ALL_BITS, current_code_section->enable_type)) == 0) {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] No match for ALL enable_bits = 0x%x, type = 0x%x, section size = %u\n", __func__,
                                        current_code_section->enable_bits, current_code_section->enable_type, section_len);
                            }
                            write_section = 0;
                        } else {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] Matched ALL enable_bits = 0x%x, type = 0x%x\n", __func__,
                                        current_code_section->enable_bits, current_code_section->enable_type);
                            }
                        }
                        break;
                    }
                case ENABLE_BITS_AND_DISABLE_BITS:
                    {
                        if ((dwc_ddrphy_phyinit_TestPIEProdEnableBits(phyctx, current_code_section->enable_bits_16,
                                        current_code_section->disable_bits_16, ENABLE_BITS_ALL_BITS, current_code_section->enable_type)) == 0) {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] No match for enable_bits = 0x%x, AND disable_bits = 0x%x, type = 0x%x, section size = %u\n", __func__,
                                        current_code_section->enable_bits_16, current_code_section->disable_bits_16, current_code_section->enable_type,
                                        section_len);
                            }
                            write_section = 0;
                        } else {
                            if (pass_num == 1) {
                                dwc_ddrphy_phyinit_cmnt ("[%s] Matched enable_bits = 0x%x, AND disable_bits = 0x%x, type = 0x%x\n", __func__,
                                        current_code_section->enable_bits_16, current_code_section->disable_bits_16, current_code_section->enable_type);
                            }
                        }
                        break;
                    }
                case RESERVED_SECTION:
                    /* Do nothing, for now */
                    break;
                default:
                    if (pass_num == 1) {
                        dwc_ddrphy_phyinit_cmnt ("[%s] Warning, unknown code section %u, ignoring, section size = %u\n",
                                __func__, current_code_section->section_type, section_len);
                    }
                    write_section = 0;
                    break;
            }
            if (write_section == 0) {
                // Skip required markers for current section
                while (marker_index < code_marker_count) {
                    code_marker_t* current_code_marker = &(code_markers[marker_index]);
                    if (current_code_marker->section_index > section_index) {
                        break;
                    }
                    current_code_marker->marker_location = NULL;
                    ++marker_index;
                }
            } else {
                // Fill in required markers for current section
                while (marker_index < code_marker_count) {
                    code_marker_t* current_code_marker = &(code_markers[marker_index]);
                    if (current_code_marker->section_index > section_index) {
                        break;
                    }
                    if (pass_num == 0) {
                        uint32_t* marker_location = current_code_marker->marker_location;
                        if (marker_location != NULL) {
                            *marker_location = current_address;
                        }
                    } else {
                        if (current_code_marker->fixup_location != NULL) {
                            // Current marker needs a call fixup, do the fixup
                            uint32_t* first_data = &(code_data[data_index]);
                            uint32_t fixup_value = *(current_code_marker->fixup_location);
                            if (fixup_value == 0u) {
                                dwc_ddrphy_phyinit_assert(0,"// [%s] Error: fixup of zero / uninit value, section %lu! [dwc_ddrphy_phyinit_LoadPieProdCode] Error PIE instruction infomation is code_markers_pie_r%d_reg[%lu]. Please use stop_address_marker instead of START_ADDRESS_MARKER_STRING to set PIE instruction marker when %s\n",
                                        __func__, section_index,((pUserInputBasic->NumRank == 1) ? 1 : 2),section_index,current_code_marker->descr_str);
                            }
                            uint32_t fixup_offset = dwc_ddrphy_phyinit_ConvertFixupSramAddress(fixup_value);
                            (*first_data) |= fixup_offset;
                        }
                    }
                    ++marker_index;
                }
                if (data_index + section_len > code_data_count) {
                    break;
                }
                if (pass_num == 1) {
                    // Call ...io_write.. to write data
                    dwc_ddrphy_phyinit_cmnt("[%s] Writing code section size = %u\n", __func__, section_len);
                    uint32_t* current_data = &(code_data[data_index]);
                    for (uint16_t j = 0; j < section_len; ++j) {
                        dwc_ddrphy_phyinit_io_write32(current_address, *current_data);
                        ++current_address;
                        ++current_data;
                    }
                } else {
                    current_address += section_len;
                }
                if (section_type == RESERVED_SECTION) {
                    if (pass_num == 1) {
                        dwc_ddrphy_phyinit_cmnt ("[%s] Moving start address from 0x%x to 0x%x, section size = %u\n", __func__,
                                current_address, current_address + current_code_section->reserved_size, current_code_section->reserved_size);
                    }
                    current_address += current_code_section->reserved_size;
                }
            }
            data_index += section_len;
            ++current_code_section;
        }
        if (pass_num == 1) {
            // Warn of mismatched input data
            if (data_index != code_data_count) {
                dwc_ddrphy_phyinit_cmnt ("[%s] Warning, sum of code section lengths (%zu) != code data count (%zu)\n", __func__, data_index, code_data_count);
            }
        } else {
            // Fill in remaining markers
            while (marker_index < code_marker_count) {
                code_marker_t* current_code_marker = &(code_markers[marker_index]);
                uint32_t* marker_location = current_code_marker->marker_location;
                if (marker_location != NULL) {
                    *marker_location = current_address;
                }
                ++marker_index;
            }
        }
    }
  dwc_ddrphy_phyinit_cmnt ("[%s] End of %s()\n", __func__, __func__);
} // End of dwc_ddrphy_phyinit_LoadPIECodeSections
/** @} */

/** @brief Find particular code marker in sorted array of code markers
 *
 * @return index of code marker, if found, otherwise UINT16_MAX
 */
uint16_t dwc_ddrphy_phyinit_FindCodeMarkerIndex(uint32_t* var_array, uint16_t var_array_count, uint16_t var_index,
                                                code_marker_t* marker_array, uint16_t marker_count, uint16_t start_index)
{
    for(uint16_t i = start_index; i < marker_count; ++i) {
        uint32_t* marker_pointer = marker_array[i].marker_location;
        uint32_t* var_pointer = &(var_array[var_index]);
        if (marker_pointer == NULL) {
            continue;
        } else if (marker_pointer == var_pointer) {
            return i;
        } else if ((marker_pointer > var_pointer) &&
                (marker_pointer > var_array)) {
            uint32_t* var_array_end = &(var_array[var_array_count]);
            if (marker_pointer < var_array_end) {
                /* If marker_pointer points within var_array    */
                /*   but past var_pointer, element is not found */
                break;
            }
        } else {
          // do nothing (else statement added for MISRA-C compliance)
        }
    }
    return UINT16_MAX;
}
/** @} */

/** @brief Set enable bits based on PUB revision
 *
 * @return Void
 */
void initRuntimeConfigEnableBits(phyinit_config_t* phyctx)
{  
    dwc_ddrphy_phyinit_cmnt ("%s Start of %s()\n", __func__, __func__);
    uint32_t enableBits = 0;
    user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
    user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
    if (pUserInputAdvanced->DisableFspOp == 0) {
        enableBits |= ENABLE_BITS_EN_FSP;
    }
    if (pUserInputBasic->NumRank == 1) {
        enableBits |= ENABLE_BITS_ONE_RANK;
    }
    if (pUserInputBasic->DramDataWidth == 8) {
        enableBits |= ENABLE_BITS_BYTE_MODE;
    }
    if (pUserInputAdvanced->DfiLoopbackEn == 1){
	    enableBits |= ENABLE_BITS_DFILOOPBACK_EN;
    }
    if (pUserInputAdvanced->SkipPwrDnInRetrain== 1){
	    enableBits |= ENABLE_BITS_SKIP_PWR_DN_IN_RETRAIN;
    }

    for (uint32_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; ++pstate) {
        if (pUserInputAdvanced->RetrainMode[pstate] == 0x4u) {
            enableBits |= ENABLE_BITS_PPT2_EN;
            break;
        }
    }
	 for (uint32_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; ++pstate) {
	       if (pUserInputAdvanced->SnoopWAEn[pstate] == 0x1u) {
            enableBits |= ENABLE_BITS_SNOOPWA_EN;
            break;
        }
    }

    PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
    if ((mb1D[phyctx->userInputBasic.FirstPState].MR28_A0 & (1u << 5)) != 0) {
        enableBits |= ENABLE_BITS_ZQ_MODE;
    }



    phyctx->runtimeConfig.enableBits[ENABLE_BITS_TYPE_GENERAL] = enableBits;
    dwc_ddrphy_phyinit_cmnt ("[%s] enableBits[%u] = 0x%08x\n", __func__, 0, enableBits);

    dwc_ddrphy_phyinit_cmnt ("[%s] End of %s()\n", __func__, __func__);

} // End of initRuntimeConfigEnableBits

/** @brief Set/Clear DfiMode CSR
 *
 * @return void
 */
void dwc_ddrphy_phyinit_programDfiMode(phyinit_config_t *phyctx, dfiMode_t mode) {
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;

  /**
   * - Program DfiMode:
   *   - Description: Enables for update and low power interfaces for DFI0 and DFI1
   *   - Fields:
   *     - Dfi0Enable
   *     - Dfi1Enable
   *   - Dependencies:
   *     - user_input_basic.NumActiveDbyteDfi0
   *     - user_input_basic.NumActiveDbyteDfi1
   */
  uint16_t skip_dfimode =1;
  uint16_t DfiMode = 0x0;
  if (!(pUserInputBasic->NumActiveDbyteDfi0 != 0 && pUserInputBasic->NumActiveDbyteDfi1 != 0)) {
    skip_dfimode=0;
  }
  if (skip_dfimode) {
    DfiMode = 0x3;
    dwc_ddrphy_phyinit_cmnt("[%s] Skip DfiMode Programming: Keeping the reset value of 0x%x\n", __func__, DfiMode); 
  } else {
    // Program DfiMode based on input argument
    if (mode == disableDfiMode) {
      // Disable unused DFI channesl

      // Set channel 0 Dfi0Enable based on userInput
      if (pUserInputBasic->NumActiveDbyteDfi0 != 0) {
        DfiMode |= csr_Dfi0Enable_MASK;
      }
     
      // Set channel 1 Dfi1Enable based on userInput
      if (pUserInputBasic->NumActiveDbyteDfi1 != 0) {
        DfiMode |= csr_Dfi1Enable_MASK;
      }      

      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DfiMode to S3 list as this
      //       CSR will be controlled in dwc_ddrphy_phyinit_userCustom_saveRetRegs.c and
      //       dwc_ddrphy_phyinit_restore_sequence.c
      dwc_ddrphy_phyinit_cmnt("[%s] Programming DfiMode to 0x%x\n", __func__, DfiMode);
      dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_DfiMode_ADDR), DfiMode);
    } else if (mode == enableDfiMode) {
      // Enable all channels for S3 retention reading

      // Set channel 0/1 Dfi{0,1}Enable
      DfiMode = (csr_Dfi1Enable_MASK | csr_Dfi0Enable_MASK);

      // Note: S3 waiver
      //       Purposely using userCustom_io_write32(), do not want to save DfiMode to S3 list as this
      //       CSR will be controlled in dwc_ddrphy_phyinit_userCustom_saveRetRegs.c and
      //       dwc_ddrphy_phyinit_restore_sequence.c
      dwc_ddrphy_phyinit_cmnt("[%s] Programming DfiMode to 0x%x\n", __func__, DfiMode);
      dwc_ddrphy_phyinit_userCustom_io_write32((tMASTER | csr_DfiMode_ADDR), DfiMode);
    } else {
    dwc_ddrphy_phyinit_assert(0, " [%s] Invalid mode = %d\n", __func__, mode);
    } 
  }
}

/** @} */

