/** \file
 *  \brief Implements function to be used in lieu of running training steps
 *  \addtogroup SrcFunc
 *  @{
 */
#include <math.h>
#include <stdlib.h>
#include "dwc_ddrphy_phyinit.h"

/** \brief This function programs registers that are normally set by training
 * firmware.
 *
 * This function is used in lieu of running 1D or 1D+2D training steps. PhyInit
 * calls this function when skip_train = 1 (SkipTrain) or 2 (DevInit). When
 * skip_train=1, PhyInit does not execute training firmware and this function is
 * called instead to program PHY registers according to DRAM timing parameters
 * specified in userInputSim data structure.  See documentation of
 * dwc_ddrphy_phyinit_struct.h file details of timing parameters available in
 * skip training.  When skip_train=2 isHMS selected, PhyInit executes training
 * firmware with SequenceCtrl set in the training firmware message block to only
 * perform DRAM device initialization. This function is then called to program
 * PHY timing registers in lieu of running training.
 *
 * \warning dwc_ddrphy_phyinit_progCsrSkipTrain() only supports zero board
 * delay model.  If system board delays are set or randomized, full 1D or 1D/2D
 * initialization flow must be executed.
 *
 * This function replaces these steps in the PHY Initialization sequence:
 *
 *  - (E) Set the PHY input clocks to the desired frequency
 *  - (F) Write the Message Block parameters for the training firmware
 *  - (G) Execute the Training Firmware
 *  - (H) Read the Message Block results
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns \c void
 */
void dwc_ddrphy_phyinit_progCsrSkipTrain(phyinit_config_t *phyctx)
{
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

  uint8_t NumDbyteActive = pRuntimeConfig->NumDbyteActive;
  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s()\n", __func__, __func__);

  /**
   * - Program CPllCtrl3
   *
   */
  uint16_t force_cal = (pRuntimeConfig->skip_train == 2) ? 0 : 1;
  uint16_t maxrange = 0x1f;
  uint16_t en_cal = 0;
  uint16_t CPllCtrl3 = (force_cal << csr_CPllForceCal_LSB) | (maxrange << csr_CPllMaxRange_LSB) | (en_cal << csr_CPllEnCal_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming CPllCtrl3::PllForceCal to 0x%x\n", __func__, force_cal);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming CPllCtrl3::PllMaxRange to 0x%x\n", __func__, maxrange);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming CPllCtrl3::PllEnCal to 0x%x\n", __func__, en_cal);
  dwc_ddrphy_phyinit_cmnt("[%s] Programming CPllCtrl3 to 0x%x\n", __func__, CPllCtrl3);
  dwc_ddrphy_phyinit_io_write32((tHMMAS | csr_CPllCtrl3_ADDR), CPllCtrl3);

  /**
   * - Program RxReplicaUICalWait
   */
  uint16_t rxUICalWait = 156;

  dwc_ddrphy_phyinit_cmnt("[%s] RxReplica Programming RxReplicaUICalWait to 0x%x\n", __func__, rxUICalWait);
  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte * c1;
    dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_RxReplicaUICalWait_ADDR), rxUICalWait);
  }

  /**
   * - Program RxClkCntl1:
   *   - Fields
   *     - EnRxClkCor
   */
  uint16_t RxClkCntl1 = csr_EnRxClkCor_MASK;

  dwc_ddrphy_phyinit_cmnt("[%s] Programming RxClkCntl1 to 0x%x\n", __func__, RxClkCntl1);

  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte * c1;
    dwc_ddrphy_phyinit_io_write32((tDBYTE | c_addr | csr_RxClkCntl1_ADDR), RxClkCntl1);
  }


  /**
   * - Program MemResetL
   *   - Fields
   *     - MemResetL
   */
  uint16_t MemResetL = csr_ProtectMemReset_MASK |  csr_MemResetLValue_MASK;
  dwc_ddrphy_phyinit_programMemResetL(phyctx, progCsrFile, MemResetL);


  dwc_ddrphy_phyinit_cmnt("[%s] End of %s()\n", __func__, __func__);
} // End of dwc_ddrphy_phyinit_progCsrSkipTrain()

/** \brief This function programs PState'able registers that are normally set by training
 * firmware.
 *
 * \warning dwc_ddrphy_phyinit_progCsrSkipTrain() only supports zero board
 * delay model.  If system board delays are set or randomized, full 1D or 1D/2D
 * initialization flow must be executed.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns void
 */
// coverity[misra_c_2012_rule_5_1_violation]
void dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(phyinit_config_t *phyctx)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  user_input_sim_t *pUserInputSim = &phyctx->userInputSim;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  


  uint16_t regData;

  dwc_ddrphy_phyinit_print("\n\n");
  dwc_ddrphy_phyinit_cmnt("/**\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("// Training firmware is *NOT* executed. This function replaces these steps\n");
  dwc_ddrphy_phyinit_cmnt("// in the PHY Initialization sequence:\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("//  (E) Set the PHY input clocks to the desired frequency\n");
  dwc_ddrphy_phyinit_cmnt("//  (F) Write the Message Block parameters for the training firmware\n");
  dwc_ddrphy_phyinit_cmnt("//  (G) Execute the Training Firmware\n");
  dwc_ddrphy_phyinit_cmnt("//  (H) Read the Message Block results\n");
  dwc_ddrphy_phyinit_cmnt("//\n");
  dwc_ddrphy_phyinit_cmnt("/**\n");
  dwc_ddrphy_phyinit_print("\n\n");

  uint32_t pstate = pRuntimeConfig->curPState;
  uint32_t p_addr = pstate << 20;
  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s(), PState=%d\n", __func__, __func__, pstate);


  uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
  int NumDbyte = pRuntimeConfig->NumDbyte;

  uint8_t NumAchn = pUserInputBasic->NumCh;
  uint8_t NumAchnActive = (pUserInputBasic->NumActiveDbyteDfi1 == 0) ? 1 : NumAchn;
  uint8_t NumDbyteActive = (NumAchnActive * pUserInputBasic->NumDbytesPerCh);
 
  int tSTAOFF = 0;
  int tPDM = 0;
  int tCASL_add = 0;

  float LcdlStepSize = (pUserInputSim->LcdlStepSizex10 / 10.0);
  int LcdlNumSteps = pUserInputSim->LcdlNumSteps;
  int LcdlTxInsertionDelay = pUserInputSim->LcdlTxInsertionDelay;
  int LcdlRxInsertionDelay = pUserInputSim->LcdlRxInsertionDelay;
  int stepsize_x10 = LcdlStepSize*10;
  float LcdlMax = LcdlStepSize*LcdlNumSteps;
  

  // Calculate total number of timing groups (ranks)
  int NumRank_total;

    NumRank_total = pUserInputBasic->NumRank_dfi0;

  dwc_ddrphy_phyinit_cmnt("[%s] NumRank_total = %d\n", __func__, NumRank_total);
  // Define UIps, StepsPerUI, FineStepPs
  float UIps;
    UIps = (1.0 / pUserInputBasic->Frequency[pstate]) * 1E6 * (pUserInputBasic->DfiFreqRatio[pstate] == 0x1 ? 0.25 : 0.125);
  int StepsPerUI = 64;
  float FineStepPs = UIps / StepsPerUI;
  dwc_ddrphy_phyinit_cmnt("[%s] UIps = %f, StepsPerUI = %d, FineStepsPs = %f\n", __func__, UIps, StepsPerUI, FineStepPs);


  /**
   * Program AC slice Tx delays
   *
   * In LPDDR5 Mode, CS pin has extra delay.
   * For LPDDR5:
   *   - CA delay (ACXTxDly)
   *   - CK delay (CKXTxDly)
   *   - no CS delay
   */
  uint16_t ACXTxDly = 1u << 6;
  uint16_t CKXTxDly = 1u << 6;


  int freq = pUserInputBasic->Frequency[pstate];
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming ACXTxDly to 0x%x\n", __func__, pstate, freq, ACXTxDly);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming CKXTxDly to 0x%x\n", __func__, pstate, freq, CKXTxDly);

  for (unsigned achn = 0; achn < NumAchnActive; achn++) {
    unsigned c_addr = achn << 12;
    dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | csr_CKXTxDly_ADDR), CKXTxDly);
    for (unsigned lane = 0; lane < 7; lane++) { // LPDDR5 CA lanes
      unsigned r_addr = lane << 8;
      dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | r_addr | csr_ACXTxDly_ADDR), ACXTxDly);
    }
    for (unsigned lane = 8; lane < 10; lane++) { // LPDDR5 CS lanes
      unsigned r_addr = lane << 8;
      dwc_ddrphy_phyinit_io_write32((p_addr | tAC | c_addr | r_addr | csr_ACXTxDly_ADDR), ACXTxDly);
    }
  }



  /**
   *
   * - Program DFIMRL per P-state according to this formula:
   *   - Dependencies:
   *     - pUserInputBasic->Frequency
   *     - pUserInputBasic->DfiFreqRatio
   *     - pUserInputBasic->PclkPtrInitVal
   *     - pUserInputSim->tDQSCK / pUserInputSim->tWCK2DQO
   *     - pUserInputSim->PHY_tDQS2DQ
   *
   *         DFIMRL = ceiling((PclkPtrInitVal_Dly + PHY_Tx_Insertion_Dly + PHY_Rx_Insertion_Dly + PHY_Rx_Fifo_dly + tDQSCK + tSTAOFF) / dficlk_ps)
   *
   * All terms in above equation specified in ps
   * tDQSCK - determine from memory model
   * tSTAOFF - determine from memory model if Dimm type is RDIMM or LRDIMM, otherwise
   * PHY_Tx_Insertion_Dly = userInputSim->LcdlTxInsertionDelay
   * PHY_Rx_Insertion_Dly = userInputSim->LcdlRxInsertionDelay
   * PHY_Rx_Fifo_Dly = 350
   * PclkPtrInitVal_Dly is a function of PclkPtrInitVal
   *
   */
  int PHY_Rx_Fifo_Dly;
  int dficlk_ps, tck_ps;
  int DFIMRL_in_ps;
  int DFIMRL_in_dficlk;
  int PclkPtrInitVal = phyctx->PclkPtrInitVal[pstate];
  int PclkPtrInitVal_Dly;
  int Read_drift;
  float Fixed_offset;

  dficlk_ps = ceil(pRuntimeConfig->tck_ps[pstate]);
  dficlk_ps += 8 - (dficlk_ps % 8);
  tck_ps = dficlk_ps;
  PHY_Rx_Fifo_Dly = ceil(((pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 2 : 1) * dficlk_ps);
  Read_drift = pUserInputSim->tWCK2DQO + pUserInputSim->PHY_tDQS2DQ;
  PclkPtrInitVal_Dly = ceil(((PclkPtrInitVal + 1) / ((((pUserInputBasic->DfiFreqRatio[pstate] == 1) && (pUserInputBasic->PllBypass[pstate] == 0)) || (pUserInputBasic->DfiFreqRatio[pstate] == 2)) ? 8.0 : 4.0)) * tck_ps);
  Fixed_offset = (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 1 : (DataRateMbps > 3200) ? 2 : 1;

  DFIMRL_in_ps = PclkPtrInitVal_Dly + LcdlTxInsertionDelay + LcdlRxInsertionDelay + PHY_Rx_Fifo_Dly + Read_drift + tSTAOFF + tCASL_add + tPDM;
  DFIMRL_in_dficlk = ceil((DFIMRL_in_ps / (dficlk_ps * 1.0)) + Fixed_offset) + mb1D[pstate].DFIMRLMargin;

  dwc_ddrphy_phyinit_cmnt("[%s] DRAM protocol = %s\n", __func__, "LPDDR5");
  dwc_ddrphy_phyinit_cmnt("[%s] DFI ratio = %s\n", __func__, pUserInputBasic->DfiFreqRatio[pstate] == 0x1 ? "1:2" : "1:4");
  dwc_ddrphy_phyinit_cmnt("[%s] CK freq (MHz) = %d\n", __func__, pUserInputBasic->Frequency[pstate]);
  dwc_ddrphy_phyinit_cmnt("[%s] tCK (ps) = %d\n", __func__, tck_ps);
  dwc_ddrphy_phyinit_cmnt("[%s] DQ UI (ps) = %f\n", __func__, UIps);
  dwc_ddrphy_phyinit_cmnt("[%s] DfiClk period (ps) = %d\n", __func__, dficlk_ps);
  dwc_ddrphy_phyinit_cmnt("[%s] PHY_Rx_Fifo_Dly (ps) = %d\n", __func__, PHY_Rx_Fifo_Dly);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlTxInsertionDelay (ps) = %d\n", __func__, LcdlTxInsertionDelay);
  dwc_ddrphy_phyinit_cmnt("[%s] LcdlRxInsertionDelay (ps) = %d\n", __func__, LcdlRxInsertionDelay);
  dwc_ddrphy_phyinit_cmnt("[%s] PllBypass = %d\n", __func__, pUserInputBasic->PllBypass[pstate]);
  dwc_ddrphy_phyinit_cmnt("[%s] PclkPtrInitVal = %d\n", __func__, PclkPtrInitVal);
  dwc_ddrphy_phyinit_cmnt("[%s] PclkPtrInitVal_Dly (ps) = %d\n", __func__, PclkPtrInitVal_Dly);
  dwc_ddrphy_phyinit_cmnt("[%s] tWCK2DQO (ps) = %d\n", __func__, pUserInputSim->tWCK2DQO);
  dwc_ddrphy_phyinit_cmnt("[%s] PHY_tDQS2DQ (ps) = %d\n", __func__, pUserInputSim->PHY_tDQS2DQ);
  dwc_ddrphy_phyinit_cmnt("[%s] Read Drift (ps) = %d\n", __func__, Read_drift);
  dwc_ddrphy_phyinit_cmnt("[%s] Fixed offset (DfiClk) = %f\n", __func__, Fixed_offset);
  dwc_ddrphy_phyinit_cmnt("[%s] DFIMRL margin (DfiClk) = %d\n", __func__, mb1D[pstate].DFIMRLMargin);
  dwc_ddrphy_phyinit_cmnt("[%s] DFIMRL (ps) = %d\n", __func__, DFIMRL_in_ps);
  dwc_ddrphy_phyinit_cmnt("[%s] DFIMRL (DfiClk) = %d\n", __func__, DFIMRL_in_dficlk);
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming HwtMRL to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], DFIMRL_in_dficlk);

  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte << 12;
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_DFIMRL_ADDR), DFIMRL_in_dficlk);
  }

  dwc_ddrphy_phyinit_io_write32((p_addr | tPPGC | csr_HwtMRL_ADDR), DFIMRL_in_dficlk);



  /**
   *
   * Program TxWckDlyTg0/Tg1 per P-State
   *
   */
  uint32_t TxWckDly_coarse, TxWckDly_coarse_default;
  uint32_t TxWckDly_fine, TxWckDly_fine_default;
  uint16_t TxWckDly;

  TxWckDly_coarse_default = (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 5 : 8;
  TxWckDly_fine_default = 0;

  TxWckDly_coarse = TxWckDly_coarse_default;
  TxWckDly_fine = TxWckDly_fine_default;

  // For AC 1/4 data rate, adjust WCK delay
  if ((pUserInputAdvanced->AcQuarterDataRate == 0x1) && (DataRateMbps>=5500)) {
    // Adjust WCK delay to aligned CK for the new >AcQuarterDataRate feature
    TxWckDly_coarse += 3;
    TxWckDly_fine   += 0x1A;
  }

  TxWckDly = (TxWckDly_coarse << 6) | TxWckDly_fine;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TxWckDlyTg0/Tg1 to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], TxWckDly);
  for (unsigned byte = 0; byte < NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte) == 0) {
      if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_TxWckDlyTg0_ADDR), TxWckDly);
      }
      if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_TxWckDlyTg1_ADDR), TxWckDly);
      }
    }
  }

  /**
   *
   * Program TxDqsDlyTg0/Tg1 per P-State
   *
   */
  uint32_t TxDqsDly_coarse;
  uint32_t TxDqsDly_fine;
  uint16_t TxDqsDly;



  //  In LP5 Mode program TxDqs in same way as TxDq for wrdata_link_ecc
  TxDqsDly_coarse = floor((pUserInputSim->tWCK2DQI + (TxWckDly_fine*FineStepPs) + UIps/2)/UIps);
  TxDqsDly_fine = ceil(fmodf((pUserInputSim->tWCK2DQI + (TxWckDly_fine*FineStepPs) + UIps/2),UIps)/FineStepPs);

  while (TxDqsDly_fine/StepsPerUI) {
    TxDqsDly_coarse += 1;
    TxDqsDly_fine -= 64;
  }

  if ((TxDqsDly_fine*FineStepPs) > LcdlMax) {
    if ((TxDqsDly_fine*FineStepPs) > UIps/2) {
      TxDqsDly_coarse += 1;
      TxDqsDly_fine = 0;
    } else if ((TxDqsDly_fine*FineStepPs) < UIps/2) {
      TxDqsDly_fine = 63;
    } else {
      // do nothing  (else statement added for MISRA-C compliance)
    }
  }

  TxDqsDly = (TxDqsDly_coarse << 6) | TxDqsDly_fine;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TxDqsDlyTg0/Tg1 to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], TxDqsDly);
  for (unsigned byte = 0; byte < NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte) == 0) {
      if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_TxDqsDlyTg0_ADDR), TxDqsDly);
      }
      if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_TxDqsDlyTg1_ADDR), TxDqsDly);
      }
    }
  }


  /**
   *
   * - Program TxDqDlyTg0/Tg1 per P-state:
   *
   */
  uint32_t TxDqDly_coarse;
  uint32_t TxDqDly_fine;
  uint16_t TxDqDly;


  TxDqDly_coarse = floor((TxWckDly_fine*FineStepPs + pUserInputSim->tWCK2DQI + UIps/2)/UIps);
  TxDqDly_fine = ceil(fmodf((TxWckDly_fine*FineStepPs + pUserInputSim->tWCK2DQI + UIps/2),UIps)/FineStepPs);

  while (TxDqDly_fine/StepsPerUI) {
    TxDqDly_coarse += 1;
    TxDqDly_fine -= 64;
  }

  if ((TxDqDly_fine*FineStepPs) > LcdlMax) {
    if ((TxDqDly_fine*FineStepPs) > UIps/2) {
      TxDqDly_coarse += 1;
      TxDqDly_fine = 0;
    } else if ((TxDqDly_fine*FineStepPs) < UIps/2) {
      TxDqDly_fine = 63;
    } else {
      // do nothing (else statement added for MISRA-C compliance)
    }
  }

  TxDqDly = (TxDqDly_coarse << 6) | TxDqDly_fine;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming TxDqDlyTg0/Tg1 to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], TxDqDly);
  for (unsigned byte = 0; byte < NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    for (unsigned lane = 0; lane < 9; lane++) {
      unsigned r_addr = lane << 8;
      if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte) == 0) {
        if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_TxDqDlyTg0_ADDR), TxDqDly);
        }
        if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_TxDqDlyTg1_ADDR), TxDqDly);
        }
      }
    }
  }


  /**
   *
   * Program RxDigStrbDlyTg0/Tg1 per P-State
   *
   */
  uint32_t  RxDigStrbDly_coarse, RxDigStrbDly_coarse_default;
  uint32_t  RxDigStrbDly_fine, RxDigStrbDly_fine_default = 32;
  int RxDigStrbDly_in_ps;
  uint16_t RxDigStrbDly;

  RxDigStrbDly_coarse_default = (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 6 : 8;
  RxDigStrbDly_in_ps = (StepsPerUI * RxDigStrbDly_coarse_default * FineStepPs) + (RxDigStrbDly_fine_default * FineStepPs) + pUserInputSim->tWCK2DQO + tSTAOFF + tCASL_add + tPDM;

  RxDigStrbDly_coarse = ((RxDigStrbDly_in_ps / FineStepPs) / StepsPerUI);
  RxDigStrbDly_fine = fmod((RxDigStrbDly_in_ps / FineStepPs), StepsPerUI);

  while (RxDigStrbDly_fine/StepsPerUI) {
    RxDigStrbDly_coarse += 1;
    RxDigStrbDly_fine -= 64;
  }

  if ((RxDigStrbDly_fine*FineStepPs) > LcdlMax) {
    if ((RxDigStrbDly_fine*FineStepPs) > UIps/2) {
      RxDigStrbDly_coarse += 1;
      RxDigStrbDly_fine = 0;
    } else if ((RxDigStrbDly_fine*FineStepPs) < UIps/2) {
      RxDigStrbDly_fine = 63;
    } else {
      //do nothing (else statement added for MISRA-C compliance)
    }
  }

  RxDigStrbDly = (RxDigStrbDly_coarse << 6) | RxDigStrbDly_fine;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming RxDigStrbDlyTg0/Tg1 to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], RxDigStrbDly);
  for (unsigned byte = 0; byte < NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    for (unsigned lane = 0; lane < 9; lane++) {
      unsigned r_addr = lane << 8;
      if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte) == 0) {
        if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_RxDigStrbDlyTg0_ADDR), RxDigStrbDly);
        }
        if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_RxDigStrbDlyTg1_ADDR), RxDigStrbDly);
        }
      }
    }
  }

  /**
   *
   * Program RxEnDlyTg0/Tg1 per P-State
   *
   */
  uint32_t RxEnDly_coarse, RxEnDly_coarse_default;
  uint32_t  RxEnDly_fine, RxEnDly_fine_default = 0;
  int RxEnDly_in_ps;
  uint16_t RxEnDly;

  RxEnDly_coarse_default = (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 4 : 6;
  RxEnDly_in_ps = (StepsPerUI * RxEnDly_coarse_default * FineStepPs) + (RxEnDly_fine_default * FineStepPs) + pUserInputSim->tWCK2DQO + tSTAOFF + tCASL_add + tPDM;
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, pUserInputSim->tWCK2DQO=%d, tSTAOFF=%d, tCASL_add=%d, tPDM=%d\n", __func__, pstate, pUserInputBasic->Frequency[pstate], pUserInputSim->tWCK2DQO, tSTAOFF, tCASL_add, tPDM);
  if ((pUserInputAdvanced->AcQuarterDataRate == 0x1) && (DataRateMbps>=5500)) {
    //Adjust RxEnDly to aligned RxEn timing for the new >AcQuarterDataRate feature
    RxEnDly_in_ps += FineStepPs * 216 ; //apply delay adjustment in RxEn
  }

  RxEnDly_coarse = ((RxEnDly_in_ps / FineStepPs) / StepsPerUI);
  RxEnDly_fine = fmod((RxEnDly_in_ps / FineStepPs), StepsPerUI);

  while (RxEnDly_fine/StepsPerUI) {
    RxEnDly_coarse += 1;
    RxEnDly_fine -= 64;
  }

  if ((mb1D[pstate].MR20_A0 & 0x3u) == 0x0) {
    RxEnDly_coarse = RxDigStrbDly_coarse;
    RxEnDly_fine = RxDigStrbDly_fine;
  }

  RxEnDly = (RxEnDly_coarse << 6) | RxEnDly_fine;

  if (pUserInputSim->RxEnDlyOffset_Reserved != 0){
    RxEnDly -= pUserInputSim->RxEnDlyOffset_Reserved / FineStepPs;
  }

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming RxEnDlyTg0/Tg1 to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], RxEnDly);
  for (unsigned byte = 0; byte < NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte) == 0) {
      if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxEnDlyTg0_ADDR), RxEnDly);
      }
      if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxEnDlyTg1_ADDR), RxEnDly);
      }
    }
  }

  /**
   *
   * Program RxClkT2UIDlyTg0/Tg1 and RxClkC2UIDlyTg0/Tg1 per P-State
   *
   */
  uint32_t RxClk2UIDly_coarse, RxClk2UIDly_coarse_default = 0;
  uint32_t RxClk2UIDly_fine, RxClk2UIDly_fine_default = 32; // fine default 0.5UI if 1/64 precision, the 0.5UI is how we say to position the RxClk in the middle of the UI
  int RxClk2UIDly_in_ps;
  uint16_t RxClk2UIDly;

  RxClk2UIDly_coarse_default = 4;

  RxClk2UIDly_in_ps = (StepsPerUI * RxClk2UIDly_coarse_default * FineStepPs) + (RxClk2UIDly_fine_default * FineStepPs) - pUserInputSim->PHY_tDQS2DQ;

  RxClk2UIDly_coarse = ((RxClk2UIDly_in_ps / FineStepPs) / StepsPerUI);
  RxClk2UIDly_fine = fmod((RxClk2UIDly_in_ps / FineStepPs), StepsPerUI);

  // Borrow one coarse delay into fine delay so RxClk tracking has margin for compensation
  // RxClkDly_fine 25 fine steps should be enough to cover all corner-cases
  // for maximum of 9600 Mbps with 40ps drift (~24.59 + 2 extra fines steps to cover potential calculation roundings). 
  if ((RxClk2UIDly_fine < 27) && (RxClk2UIDly_coarse > 0) && (pUserInputAdvanced->RxClkTrackEn[pstate] == 1)) {
    RxClk2UIDly_fine += 64;
    RxClk2UIDly_coarse -= 1;
  }

  // Borrow one coarse delay into fine delay to meet PPT2 RxClk requirement: 0.5 UI < RxClk fine delay < 1.5 UI, PPT2 only enabled when datarate >= 1600
  if ((RxClk2UIDly_fine < 31) && (RxClk2UIDly_coarse > 0) && (pUserInputAdvanced->RetrainMode[pstate] == 4) && ((pUserInputBasic->DfiFreqRatio[pstate] * pUserInputBasic->Frequency[pstate] * 2) >= 1600)) {
    RxClk2UIDly_fine += 64;
    RxClk2UIDly_coarse -= 1;
  }

  if ((mb1D[pstate].MR20_A0 & 0x3u) == 0x0) { //In Strobeless ReadMode RxClk is always 2.
    RxClk2UIDly_coarse = 2;
  }

  RxClk2UIDly = (RxClk2UIDly_coarse << 7) | RxClk2UIDly_fine;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming RxClkT2UIDlyTg0/Tg1 and RxClkC2UIDlyTg0/Tg1 to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], RxClk2UIDly);
  for (unsigned byte = 0; byte < NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    if (dwc_ddrphy_phyinit_IsDbyteDisabled(phyctx, byte) == 0) {
      for (unsigned lane = 0; lane < 9; lane++) {
        unsigned r_addr = lane << 8;
        if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_RxClkT2UIDlyTg0_ADDR), RxClk2UIDly);
        }
        if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_RxClkT2UIDlyTg1_ADDR), RxClk2UIDly);
        }
        if (((mb1D[pstate].CsPresentChA & 0x1u) >> 0) | ((mb1D[pstate].CsPresentChB & 0x1u) >> 0)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_RxClkC2UIDlyTg0_ADDR), RxClk2UIDly);
        }
        if (((mb1D[pstate].CsPresentChA & 0x2u) >> 1) | ((mb1D[pstate].CsPresentChB & 0x2u) >> 1)) {
          dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | r_addr | csr_RxClkC2UIDlyTg1_ADDR), RxClk2UIDly);
        }
      }
    }
  }



  /**
   * - Program PptDqsCntInvTrnTg0 and PptDqsCntInvTrnTg1
   *   - LPDDR4: Calculated based on DRAM tDQS2DQ and Frequency
   *   - LPDDR5: Calculated based on DRAM tWCK2DQI and Frequency
   * - Program PptWck2DqoCntInvTrnTg0 and PptWck2DqoCntInvTrnTg1 (LPDDR5 only)
   *   - Calculated based on DRAM tWCK2DQO and Frequency
   * - User input dependencies (LPDDR4):
   *   - user_input_sim_t.tDQS2DQ
   * - User input dependencies (LPDDR5):
   *   - user_input_sim_t.tWCK2DQI
   *   - user_input_sim_t.tWCK2DQO
   *   - user_input_basic_t.Frequency
   *
   * - Generic formula:
   *
   *          value = 65536 * (specified_usersim_delay_rank<rank>_chan<chan> * 2) / (2 * 2048 * UIps_int)
   *
   */
  int PptDqsCntInvTrn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  int PptWck2DqoCntInvTrn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  // Set per timing group
  for (unsigned rank = 0; rank < NumRank_total; rank++) {
    if (rank > 1) {
      break; // only Tg0 and Tg1 registers exist
    }

  

    uint32_t ratio = ((pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 2 : 4);
    PptDqsCntInvTrn[rank] = ceil((double)(128*ratio*pUserInputSim->tWCK2DQI) / (double)tck_ps);
    dwc_ddrphy_phyinit_cmnt("[%s] pUserInputSim->tWCK2DQI: %d\n", __func__, pUserInputSim->tWCK2DQI);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming PptDqsCntInvTrnTg%d to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], rank, PptDqsCntInvTrn[rank]);

    PptWck2DqoCntInvTrn[rank] = ceil((double)(128*ratio*pUserInputSim->tWCK2DQO) / (double)tck_ps);
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming PptWck2DqoCntInvTrn%d to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], rank, PptWck2DqoCntInvTrn[rank]);
  }
  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte << 12;
    for (unsigned rank = 0; rank < NumRank_total; rank++) {
      if (rank == 0) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PptDqsCntInvTrnTg0_ADDR), PptDqsCntInvTrn[rank]);
      } else if (rank == 1) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PptDqsCntInvTrnTg1_ADDR), PptDqsCntInvTrn[rank]);
      } else {
        dwc_ddrphy_phyinit_assert(0, "[%s] Error programming PptDqsCntInvTrnTg%d CSR, invalid rank=%d\n\n",__func__, rank, rank);
      }
    }
    for (unsigned rank = 0; rank < NumRank_total; rank++) {
      if (rank == 0) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PptWck2DqoCntInvTrnTg0_ADDR), PptWck2DqoCntInvTrn[rank]);
      } else if (rank == 1) {
        dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_PptWck2DqoCntInvTrnTg1_ADDR), PptWck2DqoCntInvTrn[rank]);
      } else {
        dwc_ddrphy_phyinit_assert(0, "[%s] Error programming PptWck2DqoCntInvTrnTg%d CSR, invalid rank=%d\n\n",__func__, rank, rank);
      }
    }
  }

  /**
   *
   * - Program HwtCtrl based on dram type
   *
   *   - CSRs to program:
   *     - HwtCAMode.HwtLp3CAMode
   *     - HwtCAMode.HwtD4CAMode
   *     - HwtCAMode.HwtLp4CAMode
   *     - HwtCAMode.HwtD4AltCAMode
   *     - HwtCAMode.HwtCsInvert
   *     - HwtCAMode.HwtDBIInvert
   *
   * - Dependencies
   *   - userInputBasic.DramType
   *
   */
  int HwtCtrl;
  uint32_t  HwtDBIInvert = 0;


  HwtCtrl = (HwtDBIInvert << csr_HwtDBIInvert_LSB);

  dwc_ddrphy_phyinit_cmnt("[%s] Programming HwtCtrl to 0x%x\n", __func__, HwtCtrl);
  dwc_ddrphy_phyinit_io_write32((tPPGC | csr_HwtCtrl_ADDR), HwtCtrl);

  dwc_ddrphy_phyinit_programLCDLSeed(phyctx, 1, "[phyinit_progCsrSkipTrain]");

  /**
  * - Program PllDacValIn:
  *   Set PllDacValIn to some arbitrary value
  *
  */
  uint16_t dacval_in = 0x10;

  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Memclk=%dMHz, Programming CPllDacValIn to 0x%x\n", __func__, pstate, pUserInputBasic->Frequency[pstate], dacval_in);
  dwc_ddrphy_phyinit_io_write32((p_addr | tHMMAS | csr_CPllDacValIn_ADDR), (dacval_in << csr_CPllDacValIn_LSB));

  /**
   * - Program RxReplicaPathPhaseCsrs<i>
   *   - Fields:
   *     - wdRxReplicaPathPhase
   *     - RxReplicaPathPhaseCsrs
   *   - Dependencies:
   *     - user_input_sim.tPHY_tDQS2DQ
   */
  uint16_t wdRxReplicaPathPhase[5] = {0};
  uint16_t RxReplicaPathPhaseCsrs[] = {csr_RxReplicaPathPhase0_ADDR, csr_RxReplicaPathPhase1_ADDR, csr_RxReplicaPathPhase2_ADDR, csr_RxReplicaPathPhase3_ADDR, csr_RxReplicaPathPhase4_ADDR};

  uint16_t dataClkFreq = pUserInputBasic->Frequency[pstate];  // The JEDEC term for this is Data Rate

  dataClkFreq *= (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) ? 2 : 4;

  int lcdlSeed;
  int divide_ratio;

  if (DataRateMbps < 2667) {
   lcdlSeed = (1000000 * 10 * 100) / (2 * dataClkFreq * stepsize_x10 * 100); // *100/105 is to bias the seed low
   divide_ratio = 1;
  } else {
   lcdlSeed = 2 * (1000000 * 10 * 100) / (2 * dataClkFreq * stepsize_x10 * 100); // *100/105 is to bias the seed low
   divide_ratio = 2;
  }

  if (lcdlSeed > LcdlNumSteps) {
    lcdlSeed = LcdlNumSteps;
  }
  if (lcdlSeed < 8) {
    lcdlSeed = 8;
  }

  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte << 12;
    for (uint8_t phase = 0; phase < 5; phase++) {
      wdRxReplicaPathPhase[phase] = (((phase * UIps - pUserInputSim->PHY_tDQS2DQ) / (stepsize_x10 * 0.1)) < 1) ? 0x0 :
                        (((phase * UIps - pUserInputSim->PHY_tDQS2DQ) / (stepsize_x10 * 0.1)) > 0x1ff) ? 0x1ff :
                        ceil((phase * UIps - pUserInputSim->PHY_tDQS2DQ) / (stepsize_x10 * 0.1));

      dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming DBYTE%d.RxReplicaPathPhase%d to 0x%x\n", __func__, pstate, byte, phase, wdRxReplicaPathPhase[phase]);
      dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | RxReplicaPathPhaseCsrs[phase]), wdRxReplicaPathPhase[phase]);
    }
  }

  /**
   * - Program RxReplicaCtl01::RxReplicaSelPathPhase
   */
  uint16_t RxRepPhSel = (wdRxReplicaPathPhase[0] > (lcdlSeed/(2*divide_ratio))) ? 0x0 :
              (wdRxReplicaPathPhase[1] > (lcdlSeed/(2*divide_ratio))) ? 0x1 :
              (wdRxReplicaPathPhase[2] > (lcdlSeed/(2*divide_ratio))) ? 0x2 :
              (wdRxReplicaPathPhase[3] > (lcdlSeed/(2*divide_ratio))) ? 0x3 : 0x4;
  regData = (RxRepPhSel << csr_RxReplicaSelPathPhase_LSB);

  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    unsigned c_addr = byte << 12;
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming DBYTE%d.RxReplicaCtl01::RxReplicaSelPathPhase to 0x%x\n", __func__, pstate, byte, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxReplicaCtl01_ADDR), regData);
  }

  for (unsigned byte = 0; byte < NumDbyteActive; byte++) {
    /**
     * - Program RxReplicaCtl03
     */
    float lcdlSeed_f = lcdlSeed;
    float trainedRepilcaUI_f = wdRxReplicaPathPhase[RxRepPhSel];

    unsigned c_addr = byte << 12;
    regData = (trainedRepilcaUI_f/lcdlSeed_f)*64;
    if (DataRateMbps < 2667) {
      regData = (trainedRepilcaUI_f/lcdlSeed_f)*64;
    } else {
      regData = 2*((trainedRepilcaUI_f/lcdlSeed_f)*64);
    }
    dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming DBYTE%d.RxReplicaCtl03 to 0x%x\n", __func__, pstate, byte, regData);
    dwc_ddrphy_phyinit_io_write32((p_addr | tDBYTE | c_addr | csr_RxReplicaCtl03_ADDR), regData);
  }

  // Vars for GPR7/8 for PIE to use to override ZQCalCode CSR
  uint16_t zqCalCodeOvrEn = 0x1u;
  uint16_t zqCalCodeValPU = 0x12Eu;
  uint16_t zqCalCodeValPD = 0x16du;

  /**
   * - Seq0bGPR7: Save ZQCalCodeOvrPU with OvrEn=1 for PIE to restore
   *   - Description:
   *     - Save the impedance codes for PIE to force when changing from <=3200Mbps to >3200Mbps PState switch
   *     - In Training FW, it will save real impedance values, for simulation using 0x12E as override code
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming Seq0BGPR7 to save ZQCalCodeOvrValPU=0x%x and ZQCalCodeOvrEnPU=%d\n", __func__, pstate, zqCalCodeValPU, zqCalCodeOvrEn);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BGPR7_ADDR), (zqCalCodeValPU<<csr_ZQCalCodeOvrValPU_LSB | zqCalCodeOvrEn<<csr_ZQCalCodeOvrEnPU_LSB));

  /**
   * - Seq0bGPR8: Save ZQCalCodeOvrPD with OvrEn=1 for PIE to restore
   *   - Description:
   *     - Save the impedance codes for PIE to force when changing from <=3200Mbps to >3200Mbps PState switch
   *     - In Training FW, it will save real impedance values, for simulation using 0x16D as override code
   */
  dwc_ddrphy_phyinit_cmnt("[%s] Pstate=%d, Programming Seq0BGPR8 to save ZQCalCodeOvrValPD=0x%x and ZQCalCodeOvrEnPD=%d\n", __func__, pstate, zqCalCodeValPD, zqCalCodeOvrEn);
  dwc_ddrphy_phyinit_io_write32((p_addr | tINITENG | csr_Seq0BGPR8_ADDR), (zqCalCodeValPD<<csr_ZQCalCodeOvrValPD_LSB | zqCalCodeOvrEn<<csr_ZQCalCodeOvrEnPD_LSB));

  /**
   * - TtcfControl:
   *   - Description:
   *     - Pulse the TtcfForceSendAll bit
   */
  for (unsigned byte=0; byte<NumDbyte; byte++) {
    unsigned c_addr = byte << 12;
    dwc_ddrphy_phyinit_cmnt("[%s] Programming TtcfControl[TtcfForceSendAll] to 0x1\n", __func__);
    dwc_ddrphy_phyinit_userCustom_io_write32((tDBYTE | c_addr | csr_TtcfControl_ADDR), (0x1u<<csr_TtcfForceSendAll_LSB));
    dwc_ddrphy_phyinit_cmnt("[%s] Programming TtcfControl[TtcfForceSendAll] to 0x0\n", __func__);
    dwc_ddrphy_phyinit_userCustom_io_write32((tDBYTE | c_addr | csr_TtcfControl_ADDR), (0x0u<<csr_TtcfForceSendAll_LSB));
  }


  dwc_ddrphy_phyinit_cmnt("[%s] End of %s(), PState=%d\n", __func__, __func__, pstate);
} // End of dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop()

/** @} */
