

/** \file
 * \brief initializes PhyInit input data structures to sane values.
 */
#include <string.h>
#include "dwc_ddrphy_phyinit.h"
#include "dwc_ddrphy_phyinit_LoadPieProdCode.h"

/**
 *  \addtogroup SrcFunc
 *  @{
 */

/** @brief  This is used to initialize the PhyInit structures before user defaults and overrides are applied.
 *
 * @return Void
 */
void dwc_ddrphy_phyinit_initStruct(phyinit_config_t *phyctx  /**< phyctx phyinit context */)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  user_input_sim_t *pUserInputSim = &phyctx->userInputSim;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s\n", __func__, __func__);

  PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  PMU_SMB_LPDDR5X_1D_t *shdw1D = phyctx->shdw_LPDDR5X_1D;

  memset((void *) pUserInputBasic, 0, sizeof(user_input_basic_t)); // Zero out struct contents
  memset((void *) pUserInputAdvanced, 0, sizeof(user_input_advanced_t)); // Zero out struct contents
  memset((void *) pUserInputSim, 0, sizeof(user_input_sim_t)); // Zero out struct contents

//

  // ##############################################################
  // userInputBasic - Basic Inputs the user must provide values
  // for detailed descriptions of each field see src/dwc_ddrphy_phyinit_struct.h
  // ##############################################################
  pUserInputBasic->DramType = LPDDR5;
#ifndef _SINGLE_PROTOCOL
  DramType = pUserInputBasic->DramType; // Don't change or remove this instruction
#endif
  pUserInputBasic->DimmType = UDIMM;
  pUserInputBasic->HardMacroVer = 0; //default: HardMacro family A

#ifdef _BUILD_LPDDR5X
  pUserInputBasic->Lp5xMode = 0x0001; // Don't change or remove this instruction
#else
  pUserInputBasic->Lp5xMode = 0x0000; // Don't change or remove this instruction
#endif
  pUserInputBasic->NumDbytesPerCh     = 0x0002;
  pUserInputBasic->NumCh              = 0x0002;
  pUserInputBasic->NumRank            = 0x0001;
  pUserInputBasic->NumActiveDbyteDfi0 = 0x0002;
  pUserInputBasic->NumActiveDbyteDfi1 = 0x0002;
  pUserInputBasic->NumRank_dfi0       = 0x0001; // 1 rank each controlled by dfi0 and dfi1 correspondingly
  pUserInputBasic->NumRank_dfi1       = 0x0001; // 1 rank each controlled by dfi0 and dfi1 correspondingly
  pUserInputBasic->NumPStates         = 0x0001; // 1 Pstate
  pUserInputBasic->CfgPStates         = 0x0001; // 1 Pstate, p0 enabled
  pUserInputBasic->FirstPState        = 0x0000;

  pUserInputBasic->Frequency[0]    = 400;     // 3200Mbps
  pUserInputBasic->PllBypass[0]    = 0x0000;  // PLL enabled
  pUserInputBasic->DfiFreqRatio[0] = 0x2;     // 1:4 ratio
  pUserInputBasic->PclkPtrInitVal[0] = 0x3;
  pUserInputBasic->Frequency[1]    = 400;     // 3200Mbps
  pUserInputBasic->PllBypass[1]    = 0x0000;  // PLL enabled
  pUserInputBasic->DfiFreqRatio[1] = 0x2;     // 1:4 ratio
  pUserInputBasic->PclkPtrInitVal[1] = 0x3;
  pUserInputBasic->Frequency[2]    = 400;     // 3200Mbps
  pUserInputBasic->PllBypass[2]    = 0x0000;  // PLL enabled
  pUserInputBasic->DfiFreqRatio[2] = 0x2;     // 1:4 ratio
  pUserInputBasic->PclkPtrInitVal[2] = 0x3;
  pUserInputBasic->Frequency[3]    = 400;     // 3200Mbps
  pUserInputBasic->PllBypass[3]    = 0x0000;  // PLL enabled
  pUserInputBasic->DfiFreqRatio[3] = 0x2;     // 1:4 ratio
  pUserInputBasic->PclkPtrInitVal[3] = 0x3;

  pUserInputBasic->DramDataWidth     = 0x0010; // DRAM width x16
  pUserInputBasic->MaxNumZQ          = 0x0004; // 4 DRAM devices sharing ZQ resistor
  pUserInputBasic->PclkPtrInitValOvr = 0x0;    // Do not override PclkPtrInitVal


  // ##############################################################
  // userInputAdvnaced (Optional)
  // Default values will be used if no input provided
  // ##############################################################

  // DRAM oscillator source mapping
  pUserInputAdvanced->DramByteSwap = 0x0;
  // DBYTE Rx DQ power down control when in LP state
  pUserInputAdvanced->EnLpRxDqPowerDown = 0x0;
  pUserInputAdvanced->DisRxClkCLcdl[0] = 0x0;
  pUserInputAdvanced->DisRxClkCLcdl[1] = 0x0;
  pUserInputAdvanced->DisRxClkCLcdl[2] = 0x0;
  pUserInputAdvanced->DisRxClkCLcdl[3] = 0x0;
  pUserInputAdvanced->DramStateChangeEn = 0x0;
  pUserInputAdvanced->DfiLoopbackEn = 0x0;
  pUserInputAdvanced->SkipPwrDnInRetrain = 0x0;


  pUserInputAdvanced->TxImpedanceCsCke = 50;
  // set if using SNPS Controller (default value is 0) 
  pUserInputAdvanced->UseSnpsController = 0x0;

  pUserInputAdvanced->ZcalClkDiv[0]        = 0x0;

  // Pstate 0 - Analog Settings
  pUserInputAdvanced->TxImpedanceDq[0] = 60;
  pUserInputAdvanced->TxImpedanceDqs[0] = 60;
  pUserInputAdvanced->TxImpedanceAc[0] = 40;
  pUserInputAdvanced->TxImpedanceCk[0] = 40;
  pUserInputAdvanced->TxImpedanceWCK[0] = 60;
  pUserInputAdvanced->OdtImpedanceDq[0] = 60;
  pUserInputAdvanced->OdtImpedanceDqs[0] = 60;
  pUserInputAdvanced->OdtImpedanceCa[0] = 60;
  pUserInputAdvanced->OdtImpedanceCk[0] = 60;
  pUserInputAdvanced->OdtImpedanceWCK[0] = 40;
  pUserInputAdvanced->TxSlewRiseDq[0] = 3;
  pUserInputAdvanced->TxSlewFallDq[0] = 0;
  pUserInputAdvanced->TxSlewRiseCA[0] = 3;
  pUserInputAdvanced->TxSlewFallCA[0] = 0;
  pUserInputAdvanced->TxSlewRiseCK[0] = 3;
  pUserInputAdvanced->TxSlewFallCK[0] = 0;
  pUserInputAdvanced->TxSlewRiseCS[0] = 8;
  pUserInputAdvanced->TxSlewFallCS[0] = 15;

  pUserInputAdvanced->ZcalClkDiv[1]        = 0x0;

  // Pstate 1 - Analog Settings
  pUserInputAdvanced->TxImpedanceDq[1] = 60;
  pUserInputAdvanced->TxImpedanceDqs[1] = 60;
  pUserInputAdvanced->TxImpedanceAc[1] = 40;
  pUserInputAdvanced->TxImpedanceCk[1] = 40;
  pUserInputAdvanced->TxImpedanceWCK[1] = 60;
  pUserInputAdvanced->OdtImpedanceDq[1] = 60;
  pUserInputAdvanced->OdtImpedanceDqs[1] = 60;
  pUserInputAdvanced->OdtImpedanceCa[1] = 60;
  pUserInputAdvanced->OdtImpedanceCk[1] = 60;
  pUserInputAdvanced->OdtImpedanceWCK[1] = 40;
  pUserInputAdvanced->TxSlewRiseDq[1] = 3;
  pUserInputAdvanced->TxSlewFallDq[1] = 0;
  pUserInputAdvanced->TxSlewRiseCA[1] = 3;
  pUserInputAdvanced->TxSlewFallCA[1] = 0;
  pUserInputAdvanced->TxSlewRiseCK[1] = 3;
  pUserInputAdvanced->TxSlewFallCK[1] = 0;
  pUserInputAdvanced->TxSlewRiseCS[1] = 8;
  pUserInputAdvanced->TxSlewFallCS[1] = 15;

  pUserInputAdvanced->ZcalClkDiv[2]        = 0x0;

  // Pstate 2 - Analog Settings
  pUserInputAdvanced->TxImpedanceDq[2] = 60;
  pUserInputAdvanced->TxImpedanceDqs[2] = 60;
  pUserInputAdvanced->TxImpedanceAc[2] = 40;
  pUserInputAdvanced->TxImpedanceCk[2] = 40;
  pUserInputAdvanced->TxImpedanceWCK[2] = 60;
  pUserInputAdvanced->OdtImpedanceDq[2] = 60;
  pUserInputAdvanced->OdtImpedanceDqs[2] = 60;
  pUserInputAdvanced->OdtImpedanceCa[2] = 60;
  pUserInputAdvanced->OdtImpedanceCk[2] = 60;
  pUserInputAdvanced->OdtImpedanceWCK[2] = 40;
  pUserInputAdvanced->TxSlewRiseDq[2] = 3;
  pUserInputAdvanced->TxSlewFallDq[2] = 0;
  pUserInputAdvanced->TxSlewRiseCA[2] = 3;
  pUserInputAdvanced->TxSlewFallCA[2] = 0;
  pUserInputAdvanced->TxSlewRiseCK[2] = 3;
  pUserInputAdvanced->TxSlewFallCK[2] = 0;
  pUserInputAdvanced->TxSlewRiseCS[2] = 8;
  pUserInputAdvanced->TxSlewFallCS[2] = 15;

  pUserInputAdvanced->ZcalClkDiv[3]        = 0x0;

  // Pstate 3 - Analog Settings
  pUserInputAdvanced->TxImpedanceDq[3] = 60;
  pUserInputAdvanced->TxImpedanceDqs[3] = 60;
  pUserInputAdvanced->TxImpedanceAc[3] = 40;
  pUserInputAdvanced->TxImpedanceCk[3] = 40;
  pUserInputAdvanced->TxImpedanceWCK[3] = 60;
  pUserInputAdvanced->OdtImpedanceDq[3] = 60;
  pUserInputAdvanced->OdtImpedanceDqs[3] = 60;
  pUserInputAdvanced->OdtImpedanceCa[3] = 60;
  pUserInputAdvanced->OdtImpedanceCk[3] = 60;
  pUserInputAdvanced->OdtImpedanceWCK[3] = 40;
  pUserInputAdvanced->TxSlewRiseDq[3] = 3;
  pUserInputAdvanced->TxSlewFallDq[3] = 0;
  pUserInputAdvanced->TxSlewRiseCA[3] = 3;
  pUserInputAdvanced->TxSlewFallCA[3] = 0;
  pUserInputAdvanced->TxSlewRiseCK[3] = 3;
  pUserInputAdvanced->TxSlewFallCK[3] = 0;
  pUserInputAdvanced->TxSlewRiseCS[3] = 8;
  pUserInputAdvanced->TxSlewFallCS[3] = 15;

  
  pUserInputAdvanced->ACDlyScaleGating                = 0x0000;
  
  // Disable controls for retraining
  if ((pRuntimeConfig->skip_train == 1) || (pRuntimeConfig->skip_train == 2)) { // Skip train or Devinit
    // For skip_train and devinit, DisableRetraining must be 1
    pUserInputAdvanced->DisableRetraining               = 0x1; // Not editable
  } else { // Full training
    pUserInputAdvanced->DisableRetraining               = 0x0;
  }
  // Disable controls for PclkDCA, and FSP control
  pUserInputAdvanced->DisablePclkDca    = 0x0;
  pUserInputAdvanced->DisableFspOp      = 0x0;

  // Calibration
  pUserInputAdvanced->CalInterval                   = 0x0009;
  pUserInputAdvanced->CalOnce                       = 0x0000;
  pUserInputAdvanced->CalImpedanceCurrentAdjustment = 0x0000;

  // Pipe controls
  pUserInputAdvanced->DxInPipeEnOvr   = 0x0;
  pUserInputAdvanced->DxOutPipeEnOvr  = 0x0;
  pUserInputAdvanced->AlertNPipeEnOvr = 0x0;
  pUserInputAdvanced->AcInPipeEnOvr   = 0x0;
  pUserInputAdvanced->DxRdPipeEnOvr   = 0x0;

  // PMU Ecc
  pUserInputAdvanced->DisablePmuEcc = 0x0;

  //Disbale flag for PHYINIT check if all User Inputs are set with legal values.
  pUserInputAdvanced->DisCheckAllUserInputsLegalVal = 0x0;

  // PMI, FlashCopy, CK disable value controls
  for (int pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    pUserInputAdvanced->SkipFlashCopy[pstate]                 = 0x0;
    pUserInputAdvanced->CkDisVal[pstate]                      = 0x0000;
    pUserInputAdvanced->RxDFECtrlDq[pstate]                   = 0x0;
    pUserInputAdvanced->PmuClockDiv[pstate]                   = 0x0;
    pUserInputAdvanced->PhyMstrTrainInterval[pstate]          = 0x000a;
    pUserInputAdvanced->PhyMstrMaxReqToAck[pstate]            = 0x0005;
    if ((pRuntimeConfig->skip_train == 1) || (pRuntimeConfig->skip_train == 2)) { // Skip train or Devinit
      // For skip train and devint, retraining must be disabled.
      // RxClk tracking cannot be enabled when retraining is disabled
      pUserInputAdvanced->RxClkTrackEn[pstate]                  = 0; // Not editable
    } else { // Full training
      pUserInputAdvanced->RxClkTrackEn[pstate]                  = 1;
    }
    pUserInputAdvanced->RxDqsTrackingThreshold[pstate]        = 0x1;
    pUserInputAdvanced->DqsOscRunTimeSel[pstate]              = 0x3;
    pUserInputAdvanced->RxBiasCurrentControlRxReplica[pstate] = 0x5;
    pUserInputAdvanced->DxRdPipeEn[pstate]                    = 0;
    pUserInputAdvanced->EnWck2DqoTracking[pstate]             = 0;
    pUserInputAdvanced->SnoopWAEn[pstate]                     = 0;
    pUserInputAdvanced->Lp3DramState[pstate]                  = 0;
    pUserInputAdvanced->RxBiasCurrentControlWck[pstate]       = 0x5;
    pUserInputAdvanced->DqsSampNegRxEnSense[pstate]           = 0x1;
    pUserInputAdvanced->DisCheckImpTxRx[pstate] = 1;
    pUserInputAdvanced->DisCheckDvfsqDramOdt[pstate] = 1;
    pUserInputAdvanced->CoreVddScalingMode  [pstate] = 0;
  }

  pUserInputAdvanced->DisablePhyUpdate = 0x0000;
  pUserInputAdvanced->AcQuarterDataRate = 0x0;


  pUserInputAdvanced->Lp5xDeassertDramReset  = 0x0;
  pUserInputAdvanced->Lp5xFwTinit3WaitTimex1000 = 0;
  pUserInputAdvanced->EnableSystemEcc = 0x0;
  pUserInputAdvanced->DLEPKeyCode = 0x0;
	

     pUserInputAdvanced->RxGainCtrl = 0x0;

  // Clock to pipe disable
  pUserInputAdvanced->DfiLpPipeClkDisable = 0x0;
  pUserInputAdvanced->PHYZCalPowerSaving  = 0x0;

  // IMEM/DMEM performance enable controls
  pUserInputAdvanced->IMEMLoadPerfEn = 0x1;
  pUserInputAdvanced->DMEMLoadPerfEn = 0x1;

  uint16_t RL[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint16_t WL[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint16_t nWR[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint16_t CKR[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  for (int pstate=0; pstate<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;pstate++) {

    if ( pUserInputBasic->DfiFreqRatio[pstate] == 0x1 ) {
      CKR[pstate] = 1;

      if ( pUserInputBasic->Frequency[pstate] <= 133 ) {
        RL[pstate]  = 0x0000;
        WL[pstate]  = 0x0000;
        nWR[pstate] = 0x0000;
      } else if ( pUserInputBasic->Frequency[pstate] <= 267) {
        RL[pstate]  = 0x0001;
        WL[pstate]  = 0x0001;
        nWR[pstate] = 0x0001;
      } else if ( pUserInputBasic->Frequency[pstate] <= 400) {
        RL[pstate]  = 0x0002;
        WL[pstate]  = 0x0002;
        nWR[pstate] = 0x0002;
      } else if ( pUserInputBasic->Frequency[pstate] <= 533) {
        RL[pstate]  = 0x0003;
        WL[pstate]  = 0x0003;
        nWR[pstate] = 0x0003;
      } else if ( pUserInputBasic->Frequency[pstate] <= 688) {
        RL[pstate]  = 0x0004;
        WL[pstate]  = 0x0004;
        nWR[pstate] = 0x0004;
      } else {
        RL[pstate]  = 0x0005;
        WL[pstate]  = 0x0005;
        nWR[pstate] = 0x0005;
      }
    } else {
      CKR[pstate] = 0;

      if ( pUserInputBasic->Frequency[pstate] <= 67 ) {
        RL[pstate]  = 0x0000;
        WL[pstate]  = 0x0000;
        nWR[pstate] = 0x0000;
      } else if ( pUserInputBasic->Frequency[pstate] <= 133) {
        RL[pstate]  = 0x0001;
        WL[pstate]  = 0x0001;
        nWR[pstate] = 0x0001;
      } else if ( pUserInputBasic->Frequency[pstate] <= 200) {
        RL[pstate]  = 0x0002;
        WL[pstate]  = 0x0002;
        nWR[pstate] = 0x0002;
      } else if ( pUserInputBasic->Frequency[pstate] <= 267) {
        RL[pstate]  = 0x0003;
        WL[pstate]  = 0x0003;
        nWR[pstate] = 0x0003;
      } else if ( pUserInputBasic->Frequency[pstate] <= 344) {
        RL[pstate]  = 0x0004;
        WL[pstate]  = 0x0004;
        nWR[pstate] = 0x0004;
      } else if ( pUserInputBasic->Frequency[pstate] <= 400) {
        RL[pstate]  = 0x0005;
        WL[pstate]  = 0x0005;
        nWR[pstate] = 0x0005;
      } else if ( pUserInputBasic->Frequency[pstate] <= 467) {
        RL[pstate]  = 0x0006;
        WL[pstate]  = 0x0006;
        nWR[pstate] = 0x0006;
      } else if ( pUserInputBasic->Frequency[pstate] <= 533) {
        RL[pstate]  = 0x0007;
        WL[pstate]  = 0x0007;
        nWR[pstate] = 0x0007;
      } else if ( pUserInputBasic->Frequency[pstate] <= 600) {
        RL[pstate]  = 0x0008;
        WL[pstate]  = 0x0008;
        nWR[pstate] = 0x0008;
      } else if ( pUserInputBasic->Frequency[pstate] <= 688) {
        RL[pstate]  = 0x0009;
        WL[pstate]  = 0x0009;
        nWR[pstate] = 0x0009;
      } else if ( pUserInputBasic->Frequency[pstate] <= 750) {
        RL[pstate]  = 0x000a;
        WL[pstate]  = 0x000a;
        nWR[pstate] = 0x000a;
      } else if ( pUserInputBasic->Frequency[pstate] <= 800) {
        RL[pstate]  = 0x000b;
        WL[pstate]  = 0x000b;
        nWR[pstate] = 0x000b;
      } else if ( pUserInputBasic->Frequency[pstate] <= 937) {
        RL[pstate]  = 0x000c;
        WL[pstate]  = 0x000c;
        nWR[pstate] = 0x000c;
      } else if ( pUserInputBasic->Frequency[pstate] <= 1066){
        RL[pstate]  = 0x000d;
        WL[pstate]  = 0x000d;
        nWR[pstate] = 0x000d;
      } else{
        RL[pstate]  = 0x000e;
        WL[pstate]  = 0x000e;
        nWR[pstate] = 0x000e;
      }
    }
  }

  for (int pstate=0; pstate<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;pstate++) {
    pUserInputAdvanced->RetrainMode[pstate] = 1;
  }
  

  // ##############################################################
  // Basic Message Block Variables
  // ##############################################################
  uint8_t myps;

  // ##############################################################
  // These are typically invariant across Pstate
  // ##############################################################
  uint8_t MsgMisc    = 0x06; // For fast simulation
  uint8_t Reserved00 = 0x0;  // Set Reserved00[7]   = 1 (If using T28 attenuated receivers)
                             // Set Reserved00[6:0] = 0 (Reserved; must be programmed to 0)

  // 2D Training Miscellaneous Control
  // Train2DMisc[0]: Print Verbose 2D Eye Contour
  //   0 = Do Not Print Verbose Eye Contour  (default behavior)
  // Train2DMisc[1]: Print Verbose Eye Optimization Output
  //   0 = Do Not Print Verbose Eye Optimization Output  (default behavior)
  // Train2DMisc[5:2]: Iteration Count for Optimization Algorithm
  // Iteration count = Train2DMisc[5:2] << 1
  // iteration count == 2 early termination
  // Train2DMisc[7:6]: Number of Seeds for Optimization Algorithm
  // 0 = 2 seeds, left and right of center, default behavior
  // Train2DMisc[8]: Print Eye Contours prior to optimization
  // 0 = Do Not Print Eye Contours prior to optimization (default behavior)
  // Train2DMisc[9]: Print full eye contours (instead of half)
  // 0 = Print Half Eye Contours (default behavior)
  // Train2DMisc[10]: Use weighted mean algorithm for optimization of RX compounded eyes with DFE
  // 0 = Use largest empty circle hill climb (default behavior)
  // Train2DMisc[12:11]: Weighted mean algorithm bias function.
  // 0 = Use regular weighted mean
  uint16_t Train2DMisc = (0x0001u << 2); // Early Termination

  uint8_t HdtCtrl = 0xff;
  uint8_t DFIMRLMargin = 0x02;
  uint8_t CATerminatingRankChA = 0x00; // Usually Rank0 is terminating rank
  uint8_t CATerminatingRankChB = 0x00; // Usually Rank0 is terminating rank

  // ##############################################################
  // These typically change across Pstate
  // ##############################################################
  uint16_t SequenceCtrl[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr1[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr2[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr3[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr10[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr11[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr12[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr13[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr14[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr15[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr16[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr17_rank0[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr17_rank1[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr18[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr19[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr20[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr21[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr22[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr24[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr28[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr41[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr58[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr69[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr70[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr71[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr72[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr73[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];
  uint8_t mr74[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE];

  for (int pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    SequenceCtrl[pstate] = 0x121f; // Training steps to run in PState 0
    pUserInputAdvanced->TrainSequenceCtrl[pstate] =  SequenceCtrl[pstate];
  }

  pUserInputAdvanced->DtoEnable = 0;
  pUserInputAdvanced->DisZCalOnDataRate = 0x1u;
  pUserInputAdvanced->HalfTxCalCode = 0x0u;

  uint16_t ZqModeDefault = 0x0;

  uint16_t PDFEC[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  // Corresponding to MR21[5], setting to 1 will enable LPDDR5 READ data copy function, default is disabling 
  uint16_t RdcfeDis[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t CaOdtDis_r0[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WECC[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t SocOdt_r1[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x4, 0x4, 0x4, 0x4 };
  uint16_t DqOdt[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x4, 0x4, 0x4, 0x4 };
  uint16_t PDDS[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x6, 0x6, 0x6, 0x6 };
  uint16_t DvfsC[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DqDnPreEmUB[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WckOdt[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DqUpPreEmLB[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t ZqMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { ZqModeDefault, ZqModeDefault, ZqModeDefault, ZqModeDefault };
  uint16_t VrefDqU[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x50, 0x50, 0x50, 0x50 };
  uint16_t PPRE[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t CkOdtDis_r0[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t RECC[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DvfsQ[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WckFm[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t CkMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DFEQU[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DqDnPreEmLB[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DFEQL[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t VDLC[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t CsOdtDis_r0[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t NtDqOdt[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x3, 0x3, 0x3, 0x3 };
  uint16_t WckPst[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x1, 0x1, 0x1, 0x1 };
  uint16_t RdqsPst[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x1, 0x1, 0x1, 0x1 };
  uint16_t CaOdtDis_r1[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x1, 0x1, 0x1, 0x1 };
  uint16_t RdqsMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x2, 0x2, 0x2, 0x2 };
  uint16_t DbiWr[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DqUpPreEmUB[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t Wck2DqFm[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t CaOdt[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x4, 0x4, 0x4, 0x4 };
  uint16_t CsOdtDis_r1[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t RdqsPre[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x1, 0x1, 0x1, 0x1 };
  uint16_t VrefCa[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x50, 0x50, 0x50, 0x50 };
  uint16_t CsOdtT[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WxfeDis[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WckMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t DbiRd[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t SocOdt_r0[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x4, 0x4, 0x4, 0x4 };
  uint16_t VrefDqL[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x50, 0x50, 0x50, 0x50 };
  uint16_t BKBG[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x1, 0x1, 0x1, 0x1 };
  uint16_t CsOdtOp[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WLS[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t CkOdtDis_r1[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x1, 0x1, 0x1, 0x1 };
  uint16_t NtOdt[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  // Corresponding to MR21[4], setting to 1 will enable LPDDR5 WRITE data copy function, default is disabling 
  uint16_t WdcfeDis[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t WckOn[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };
  uint16_t RpstMode[DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE] = { 0x0, 0x0, 0x0, 0x0 };

  uint16_t x8OdtL_r0 = 0x0;
  uint16_t x8OdtL_r1 = 0x0;
  uint16_t x8OdtU_r0 = 0x1;
  uint16_t x8OdtU_r1 = 0x1;

  // ##############################################################
  // 95% of users will not need to edit below
  // ##############################################################
  // MR bit packing for LPDDR5
  for ( myps = 0; myps < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE ; myps++) {
    mr1[myps] =
        ( (CkMode[myps]                              << 3) & 0x08u) | // CK mode
        ( (WL[myps]                                  << 4) & 0xF0u) ; // WL

    mr2[myps] =
        ( (RL[myps]                                  << 0) & 0x0Fu) | // RL and nRTP
        ( (nWR[myps]                                 << 4) & 0xF0u) ; // nWR

    mr3[myps] =
        ( (PDDS[myps]                                << 0) & 0x07u) | // PDDS
        ( (BKBG[myps]                                << 3) & 0x18u) | // BK/BG
        ( (WLS[myps]                                 << 5) & 0x20u) | // WLS
        ( (DbiRd[myps]                               << 6) & 0x40u) | // DBI-RD
        ( (DbiWr[myps]                               << 7) & 0x80u) ; // DBI-WR

    mr10[myps] =
        ( (RpstMode[myps]                            << 0) & 0x01u) | // RPST Mode
        ( (WckPst[myps]                              << 2) & 0x0Cu) | // WCK PST
        ( (RdqsPre[myps]                             << 4) & 0x30u) | // RDQS PRE
        ( (RdqsPst[myps]                             << 6) & 0xC0u) ; // RDQS PST

    mr11[myps] =
        ( (DqOdt[myps]                               << 0) & 0x07u) | // DQ ODT
        ( (NtOdt[myps]                               << 3) & 0x08u) | // NT-ODT
        ( (CaOdt[myps]                               << 4) & 0x70u) | // CA ODT
        ( (CsOdtOp[myps]                             << 7) & 0x80u) ; // CS ODT OP

    mr12[myps] =
        ( (VrefCa[myps]                              << 0) & 0x7Fu) | // VREF CA
        ( (0x0u                                       << 7) & 0x80u) ; // VBS

    mr13[myps] =
        ( (0x0u                                       << 0) & 0x03u) | // Thermal Offset
        ( (0x0u                                       << 2) & 0x04u) | // VRO
        ( (0x0u                                       << 5) & 0x20u) | // DMD
        ( (0x0u                                       << 6) & 0x40u) | // CBT Mode
        ( (0x0u                                       << 7) & 0x80u) ; // Dual VDD2

    mr14[myps] =
        ( (VrefDqL[myps]                             << 0) & 0x7Fu) | // VREF DQ 7:0
        ( (VDLC[myps]                                << 7) & 0x80u) ; // VDLC

    mr15[myps] =
        ( (VrefDqU[myps]                             << 0) & 0x7Fu) ; // VREF DQ 15:8

    mr16[myps] =
        ( (0x0u                                       << 0) & 0x03u) | // FSP-WR
        ( (0x0u                                       << 2) & 0x0Cu) | // FSP-OP
        ( (0x0u                                       << 4) & 0x30u) | // CBT
        ( (0x0u                                       << 6) & 0x40u) | // VRCG
        ( (0x0u                                       << 7) & 0x80u) ; // CBT-Phase

    mr17_rank0[myps] =
        ( (SocOdt_r0[myps]                              << 0) & 0x07u) | // SOC ODT
        ( (CkOdtDis_r0[myps]                            << 3) & 0x08u) | // ODTD-CK
        ( (CsOdtDis_r0[myps]                            << 4) & 0x10u) | // ODTD-CS
        ( (CaOdtDis_r0[myps]                            << 5) & 0x20u) | // ODTD-CA
        ( (x8OdtL_r0                                    << 6) & 0x40u) | // x8ODTD Lower
        ( (x8OdtU_r0                                    << 7) & 0x80u) ; // x8ODTD Upper

    mr17_rank1[myps] =
        ( (SocOdt_r1[myps]                              << 0) & 0x07u) | // SOC ODT
        ( (CkOdtDis_r1[myps]                            << 3) & 0x08u) | // ODTD-CK
        ( (CsOdtDis_r1[myps]                            << 4) & 0x10u) | // ODTD-CS
        ( (CaOdtDis_r1[myps]                            << 5) & 0x20u) | // ODTD-CA
        ( (x8OdtL_r1                                    << 6) & 0x40u) | // x8ODTD Lower
        ( (x8OdtU_r1                                    << 7) & 0x80u) ; // x8ODTD Upper

    mr18[myps] =
        ( (WckOdt[myps]                              << 0) & 0x07u) | // WCK ODT
        ( (WckFm[myps]                               << 3) & 0x08u) | // WCK FM
        ( (WckOn[myps]                               << 4) & 0x10u) | // WCK ON
        ( (0x0u                                       << 6) & 0x40u) | // WCK2CK Leveling
        ( (CKR[myps]                                 << 7) & 0x80u) ; // CKR

    mr19[myps] =
        ( (DvfsC[myps]                               << 0) & 0x03u) | // DVFSC
        ( (DvfsQ[myps]                               << 2) & 0x0Cu) | // DVFSQ
        ( (Wck2DqFm[myps]                            << 4) & 0x10u) | // WCK2DQ OSC FM
        ( (CsOdtT[myps]                                 << 6) & 0xC0u); // Cs ODT (CS termination)

    mr20[myps] =
        ( (RdqsMode[myps]                            << 0) & 0x03u) | // RDQS
        ( (WckMode[myps]                             << 2) & 0x0Cu) | // WCK mode
        ( (0x0u                                       << 4) & 0x10u) | // MRWDU
        ( (0x0u                                       << 5) & 0x20u) | // MRWDL
        ( (0x0u                                       << 6) & 0x40u) | // RDC DMI mode
        ( (0x0u                                       << 7) & 0x80u) ; // RDC DQ mode

    mr21[myps] =
        ( (WdcfeDis[myps]                            << 4) & 0x10u) | // WDCFE
        ( (RdcfeDis[myps]                            << 5) & 0x20u) | // RDCFE
        ( (WxfeDis[myps]                             << 6) & 0x40u) ; // WXFE

    mr22[myps] =
        ( (WECC[myps]                                << 4) & 0x30u) | // WECC
        ( (RECC[myps]                                << 6) & 0xC0u) ; // RECC

    mr24[myps] =
        ( (DFEQL[myps]                               << 0) & 0x07u) | // DFEQL
        ( (DFEQU[myps]                               << 4) & 0x70u) ; // DFEQU

    mr28[myps] =
        ( (0x0u                                       << 0) & 0x01u) | // ZQ Reset
        ( (0x0u                                       << 1) & 0x02u) | // ZQ Stop
        ( (0x1u                                       << 2) & 0x0Cu) | // ZQ Interval
        ( (ZqMode[myps]                              << 5) & 0x20u) ; // ZQ Mode

    mr41[myps] =
        ( (PDFEC[myps]                               << 0) & 0x01u) | // PDFEC
        ( (PPRE[myps]                                << 4) & 0x10u) | // PPRE
        ( (NtDqOdt[myps]                             << 5) & 0xE0u) ; // NT DQ ODT

    mr58[myps] =
        ( (DqUpPreEmLB[myps]                         << 0u) & 0x03u) | // DQ Up Emphasis LB
        ( (DqDnPreEmLB[myps]                         << 2u) & 0x0Cu) | // DQ Dn Emphasis LB
        ( (DqUpPreEmUB[myps]                         << 4u) & 0x30u) | // DQ Up Emphasis UB
        ( (DqDnPreEmUB[myps]                         << 6u) & 0xC0u) ; // DQ Dn Emphasis UB

    mr69[myps] = 0x0;
    mr70[myps] = 0x0;
    mr71[myps] = 0x0;
    mr72[myps] = 0x0;
    mr73[myps] = 0x0;
    mr74[myps] = 0x0;
  }

  // 1D message block defaults
  for (myps=0; myps<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; myps++) {
    // -- Pstate is a derived input set in calcMb
    //mb1D[myps].Pstate               = myps;
    mb1D[myps].SequenceCtrl         = SequenceCtrl[myps];
    mb1D[myps].HdtCtrl              = HdtCtrl;
    mb1D[myps].MsgMisc              = MsgMisc;
    mb1D[myps].Train2DMisc          = Train2DMisc;
    mb1D[myps].Reserved00           = Reserved00;
    mb1D[myps].DFIMRLMargin         = DFIMRLMargin;
    mb1D[myps].EnabledDQsChA       = pUserInputBasic->NumActiveDbyteDfi0 * 8 ;
    mb1D[myps].EnabledDQsChB       = pUserInputBasic->NumActiveDbyteDfi1 * 8 ;
    mb1D[myps].Disable2D            = 0x0000;
    mb1D[myps].CsPresentChA         = (2==pUserInputBasic->NumRank_dfi0) ? 0x3 : pUserInputBasic->NumRank_dfi0;
    mb1D[myps].CsPresentChB         = (2==pUserInputBasic->NumRank_dfi1) ? 0x3 : pUserInputBasic->NumRank_dfi1;
    mb1D[myps].X8Mode               = 0x0000;
    mb1D[myps].VrefInc              = 0x1;
    mb1D[myps].CaTrainAltUpdate     = 0x0;
    mb1D[myps].CATrainOpt           = 0x0000;
#ifdef _BUILD_LPDDR5X
    mb1D[myps].LP5XMode             = 0x0001; // Don't change or remove this instruction
#else
    mb1D[myps].LP5XMode             = 0x0000; // Don't change or remove this instruction
#endif
    mb1D[myps].TxDFETrainOpt    = mr41[myps] & 0x1u;
    mb1D[myps].MR1_A0               = mr1[myps];
    mb1D[myps].MR1_A1               = mr1[myps];
    mb1D[myps].MR1_B0               = mr1[myps];
    mb1D[myps].MR1_B1               = mr1[myps];
    mb1D[myps].MR2_A0               = mr2[myps];
    mb1D[myps].MR2_A1               = mr2[myps];
    mb1D[myps].MR2_B0               = mr2[myps];
    mb1D[myps].MR2_B1               = mr2[myps];
    mb1D[myps].MR3_A0               = mr3[myps];
    mb1D[myps].MR3_A1               = mr3[myps];
    mb1D[myps].MR3_B0               = mr3[myps];
    mb1D[myps].MR3_B1               = mr3[myps];
    mb1D[myps].MR10_A0              = mr10[myps];
    mb1D[myps].MR10_A1              = mr10[myps];
    mb1D[myps].MR10_B0              = mr10[myps];
    mb1D[myps].MR10_B1              = mr10[myps];
    mb1D[myps].MR11_A0              = mr11[myps];
    mb1D[myps].MR11_A1              = mr11[myps];
    mb1D[myps].MR11_B0              = mr11[myps];
    mb1D[myps].MR11_B1              = mr11[myps];
    mb1D[myps].MR12_A0              = mr12[myps];
    mb1D[myps].MR12_A1              = mr12[myps];
    mb1D[myps].MR12_B0              = mr12[myps];
    mb1D[myps].MR12_B1              = mr12[myps];
    mb1D[myps].MR13_A0              = mr13[myps];
    mb1D[myps].MR13_A1              = mr13[myps];
    mb1D[myps].MR13_B0              = mr13[myps];
    mb1D[myps].MR13_B1              = mr13[myps];
    mb1D[myps].MR14_A0              = mr14[myps];
    mb1D[myps].MR14_A1              = mr14[myps];
    mb1D[myps].MR14_B0              = mr14[myps];
    mb1D[myps].MR14_B1              = mr14[myps];
    mb1D[myps].MR15_A0              = mr15[myps];
    mb1D[myps].MR15_A1              = mr15[myps];
    mb1D[myps].MR15_B0              = mr15[myps];
    mb1D[myps].MR15_B1              = mr15[myps];
    mb1D[myps].MR16_A0              = mr16[myps];
    mb1D[myps].MR16_A1              = mr16[myps];
    mb1D[myps].MR16_B0              = mr16[myps];
    mb1D[myps].MR16_B1              = mr16[myps];
    mb1D[myps].MR17_A0              = mr17_rank0[myps];
    mb1D[myps].MR17_A1              = mr17_rank1[myps];
    mb1D[myps].MR17_B0              = mr17_rank0[myps];
    mb1D[myps].MR17_B1              = mr17_rank1[myps];
    mb1D[myps].MR18_A0              = mr18[myps];
    mb1D[myps].MR18_A1              = mr18[myps];
    mb1D[myps].MR18_B0              = mr18[myps];
    mb1D[myps].MR18_B1              = mr18[myps];
    mb1D[myps].MR19_A0              = mr19[myps];
    mb1D[myps].MR19_A1              = mr19[myps];
    mb1D[myps].MR19_B0              = mr19[myps];
    mb1D[myps].MR19_B1              = mr19[myps];
    mb1D[myps].MR20_A0              = mr20[myps];
    mb1D[myps].MR20_A1              = mr20[myps];
    mb1D[myps].MR20_B0              = mr20[myps];
    mb1D[myps].MR20_B1              = mr20[myps];
    mb1D[myps].MR21_A0              = mr21[myps];
    mb1D[myps].MR21_A1              = mr21[myps];
    mb1D[myps].MR21_B0              = mr21[myps];
    mb1D[myps].MR21_B1              = mr21[myps];
    mb1D[myps].MR22_A0              = mr22[myps];
    mb1D[myps].MR22_A1              = mr22[myps];
    mb1D[myps].MR22_B0              = mr22[myps];
    mb1D[myps].MR22_B1              = mr22[myps];
    mb1D[myps].MR24_A0              = mr24[myps];
    mb1D[myps].MR24_A1              = mr24[myps];
    mb1D[myps].MR24_B0              = mr24[myps];
    mb1D[myps].MR24_B1              = mr24[myps];
    mb1D[myps].MR28_A0              = mr28[myps];
    mb1D[myps].MR28_A1              = mr28[myps];
    mb1D[myps].MR28_B0              = mr28[myps];
    mb1D[myps].MR28_B1              = mr28[myps];
    mb1D[myps].MR41_A0              = mr41[myps];
    mb1D[myps].MR41_A1              = mr41[myps];
    mb1D[myps].MR41_B0              = mr41[myps];
    mb1D[myps].MR41_B1              = mr41[myps];
    mb1D[myps].MR58_A0              = mr58[myps];
    mb1D[myps].MR58_A1              = mr58[myps];
    mb1D[myps].MR58_B0              = mr58[myps];
    mb1D[myps].MR58_B1              = mr58[myps];
    mb1D[myps].MR69_A0              = mr69[myps];
    mb1D[myps].MR69_A1              = mr69[myps];
    mb1D[myps].MR69_B0              = mr69[myps];
    mb1D[myps].MR69_B1              = mr69[myps];
    mb1D[myps].MR70_A0              = mr70[myps];
    mb1D[myps].MR70_A1              = mr70[myps];
    mb1D[myps].MR70_B0              = mr70[myps];
    mb1D[myps].MR70_B1              = mr70[myps];
    mb1D[myps].MR71_A0              = mr71[myps];
    mb1D[myps].MR71_A1              = mr71[myps];
    mb1D[myps].MR71_B0              = mr71[myps];
    mb1D[myps].MR71_B1              = mr71[myps];
    mb1D[myps].MR72_A0              = mr72[myps];
    mb1D[myps].MR72_A1              = mr72[myps];
    mb1D[myps].MR72_B0              = mr72[myps];
    mb1D[myps].MR72_B1              = mr72[myps];
    mb1D[myps].MR73_A0              = mr73[myps];
    mb1D[myps].MR73_A1              = mr73[myps];
    mb1D[myps].MR73_B0              = mr73[myps];
    mb1D[myps].MR73_B1              = mr73[myps];
    mb1D[myps].MR74_A0              = mr74[myps];
    mb1D[myps].MR74_A1              = mr74[myps];
    mb1D[myps].MR74_B0              = mr74[myps];
    mb1D[myps].MR74_B1              = mr74[myps];
    mb1D[myps].CATerminatingRankChA = CATerminatingRankChA;
    mb1D[myps].CATerminatingRankChB = CATerminatingRankChB;
    mb1D[myps].Rx1UIThreshold = 1600;
    mb1D[myps].Rx2UIThreshold = 3200;
    memset((void *) &shdw1D[myps], 0, sizeof(PMU_SMB_LPDDR5X_1D_t)); // Zero out struct contents
  } // myps


  // ##############################################################
  // userInputSim - Dram/Dimm Timing Parameters the user must
  // provide value if applicable
  // ##############################################################
  pUserInputSim->tWCK2DQO = 1000;
  pUserInputSim->tWCK2DQI = 500;
  pUserInputSim->tWCK2CK = 0;

  // ##############################################################
  // Set to be compatible with maximum design frequency
  // ##############################################################
  pUserInputSim->PHY_tDQS2DQ = 285; // 200ps DQS2DQ skew + 84.5 ps LCDL insertion delay.

  // ##############################################################
  // userInputSim - Set LCDL parameters to default
  // ##############################################################
  pUserInputSim->LcdlNumSteps         = 511;
  pUserInputSim->LcdlStepSizex10      = 30;
  pUserInputSim->LcdlTxInsertionDelay = 85;
  pUserInputSim->LcdlRxInsertionDelay = 85;


  pUserInputSim->RxEnDlyOffset_Reserved = 0x0;

  // ##############################################################
  // Initialize phyinit_config_t.AcsmMrkrCnt[] array values to 0's
  // ##############################################################
  for (uint8_t acsmIdx=0; acsmIdx<DWC_DDRPHY_PHYINIT_NUM_ACSM_MARKERS; acsmIdx++) {
    phyctx->AcsmMrkrCnt[acsmIdx] = 0x0;
  }


  dwc_ddrphy_phyinit_cmnt("[%s] End of %s\n", __func__, __func__);
}

/** @} */
