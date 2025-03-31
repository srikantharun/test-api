/** \file
 *  \brief Implements function to read PhyInit data structures
 */
#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** \addtogroup SrcFunc
 *  @{
 */

/** @brief API to read PhyInit data structures
 *
 *  This function can be used to read user_input_basic, user_input_advanced and
 *  user_input_sim data structures.
 *
 *  Some fields are defined as arrays in the data structure. Example to set
 *  PllBypass for Pstate 3:
 *
 *  @code{.c}
 *  dwc_ddrphy_phyinit_getUserInput("PllBypass[3]", 0x1);
 *  @endcode
 *
 *  \note field strings do not overlap between PhyInit structures.
 *
 *  @param[in]   phyctx  PhyInit context
 *
 *  @param[in]   field   A string representing the field to read. bracket
 *  notation can be used to set array fields. example  string: "PllBypass[0]"
 *  set the field UserInputBasic.PllBypass[0].
 *  fields is an array,
 *
 *  @return field value on success. -1 when string does not match fields in any oh PhyInit
 *  data structures.
 */
int dwc_ddrphy_phyinit_getUserInput(phyinit_config_t *phyctx, char *field)
{
	user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
	user_input_sim_t *pUserInputSim = &phyctx->userInputSim;

	if (strcmp(field, "NumPStates") == 0) {
		return pUserInputBasic->NumPStates;
	}
	else if (strcmp(field, "NumRank_dfi0") == 0) {
		return pUserInputBasic->NumRank_dfi0;
	}
	else if (strcmp(field, "HardMacroVer") == 0) {
		return pUserInputBasic->HardMacroVer;
	}
	else if (strcmp(field, "NumCh") == 0) {
		return pUserInputBasic->NumCh;
	}
	else if (strcmp(field, "DimmType") == 0) {
		return pUserInputBasic->DimmType;
	}
	else if (strcmp(field, "Lp5xMode") == 0) {
		return pUserInputBasic->Lp5xMode;
	}
	else if (strcmp(field, "DramType") == 0) {
		return pUserInputBasic->DramType;
	}
	else if (strcmp(field, "DfiFreqRatio[0]") == 0) {
		return pUserInputBasic->DfiFreqRatio[0];
	}
	else if (strcmp(field, "DfiFreqRatio[1]") == 0) {
		return pUserInputBasic->DfiFreqRatio[1];
	}
	else if (strcmp(field, "DfiFreqRatio[2]") == 0) {
		return pUserInputBasic->DfiFreqRatio[2];
	}
	else if (strcmp(field, "DfiFreqRatio[3]") == 0) {
		return pUserInputBasic->DfiFreqRatio[3];
	}
	else if (strcmp(field, "FirstPState") == 0) {
		return pUserInputBasic->FirstPState;
	}
	else if (strcmp(field, "NumActiveDbyteDfi1") == 0) {
		return pUserInputBasic->NumActiveDbyteDfi1;
	}
	else if (strcmp(field, "NumRank") == 0) {
		return pUserInputBasic->NumRank;
	}
	else if (strcmp(field, "DramDataWidth") == 0) {
		return pUserInputBasic->DramDataWidth;
	}
	else if (strcmp(field, "CfgPStates") == 0) {
		return pUserInputBasic->CfgPStates;
	}
	else if (strcmp(field, "PclkPtrInitValOvr") == 0) {
		return pUserInputBasic->PclkPtrInitValOvr;
	}
	else if (strcmp(field, "Frequency[0]") == 0) {
		return pUserInputBasic->Frequency[0];
	}
	else if (strcmp(field, "Frequency[1]") == 0) {
		return pUserInputBasic->Frequency[1];
	}
	else if (strcmp(field, "Frequency[2]") == 0) {
		return pUserInputBasic->Frequency[2];
	}
	else if (strcmp(field, "Frequency[3]") == 0) {
		return pUserInputBasic->Frequency[3];
	}
	else if (strcmp(field, "PllBypass[0]") == 0) {
		return pUserInputBasic->PllBypass[0];
	}
	else if (strcmp(field, "PllBypass[1]") == 0) {
		return pUserInputBasic->PllBypass[1];
	}
	else if (strcmp(field, "PllBypass[2]") == 0) {
		return pUserInputBasic->PllBypass[2];
	}
	else if (strcmp(field, "PllBypass[3]") == 0) {
		return pUserInputBasic->PllBypass[3];
	}
	else if (strcmp(field, "NumRank_dfi1") == 0) {
		return pUserInputBasic->NumRank_dfi1;
	}
	else if (strcmp(field, "NumDbytesPerCh") == 0) {
		return pUserInputBasic->NumDbytesPerCh;
	}
	else if (strcmp(field, "PclkPtrInitVal[0]") == 0) {
		return pUserInputBasic->PclkPtrInitVal[0];
	}
	else if (strcmp(field, "PclkPtrInitVal[1]") == 0) {
		return pUserInputBasic->PclkPtrInitVal[1];
	}
	else if (strcmp(field, "PclkPtrInitVal[2]") == 0) {
		return pUserInputBasic->PclkPtrInitVal[2];
	}
	else if (strcmp(field, "PclkPtrInitVal[3]") == 0) {
		return pUserInputBasic->PclkPtrInitVal[3];
	}
	else if (strcmp(field, "MaxNumZQ") == 0) {
		return pUserInputBasic->MaxNumZQ;
	}
	else if (strcmp(field, "NumActiveDbyteDfi0") == 0) {
		return pUserInputBasic->NumActiveDbyteDfi0;
	}
	else if (strcmp(field, "CalImpedanceCurrentAdjustment") == 0) {
		return pUserInputAdvanced->CalImpedanceCurrentAdjustment;
	}
	else if (strcmp(field, "CalOnce") == 0) {
		return pUserInputAdvanced->CalOnce;
	}
	else if (strcmp(field, "DMEMLoadPerfEn") == 0) {
		return pUserInputAdvanced->DMEMLoadPerfEn;
	}
	else if (strcmp(field, "TxSlewRiseCA[0]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCA[0];
	}
	else if (strcmp(field, "TxSlewRiseCA[1]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCA[1];
	}
	else if (strcmp(field, "TxSlewRiseCA[2]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCA[2];
	}
	else if (strcmp(field, "TxSlewRiseCA[3]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCA[3];
	}
	else if (strcmp(field, "RxGainCtrl") == 0) {
		return pUserInputAdvanced->RxGainCtrl;
	}
	else if (strcmp(field, "DramStateChangeEn") == 0) {
		return pUserInputAdvanced->DramStateChangeEn;
	}
	else if (strcmp(field, "TxSlewFallCK[0]") == 0) {
		return pUserInputAdvanced->TxSlewFallCK[0];
	}
	else if (strcmp(field, "TxSlewFallCK[1]") == 0) {
		return pUserInputAdvanced->TxSlewFallCK[1];
	}
	else if (strcmp(field, "TxSlewFallCK[2]") == 0) {
		return pUserInputAdvanced->TxSlewFallCK[2];
	}
	else if (strcmp(field, "TxSlewFallCK[3]") == 0) {
		return pUserInputAdvanced->TxSlewFallCK[3];
	}
	else if (strcmp(field, "OdtImpedanceCk[0]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCk[0];
	}
	else if (strcmp(field, "OdtImpedanceCk[1]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCk[1];
	}
	else if (strcmp(field, "OdtImpedanceCk[2]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCk[2];
	}
	else if (strcmp(field, "OdtImpedanceCk[3]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCk[3];
	}
	else if (strcmp(field, "Lp5xDeassertDramReset") == 0) {
		return pUserInputAdvanced->Lp5xDeassertDramReset;
	}
	else if (strcmp(field, "OdtImpedanceWCK[0]") == 0) {
		return pUserInputAdvanced->OdtImpedanceWCK[0];
	}
	else if (strcmp(field, "OdtImpedanceWCK[1]") == 0) {
		return pUserInputAdvanced->OdtImpedanceWCK[1];
	}
	else if (strcmp(field, "OdtImpedanceWCK[2]") == 0) {
		return pUserInputAdvanced->OdtImpedanceWCK[2];
	}
	else if (strcmp(field, "OdtImpedanceWCK[3]") == 0) {
		return pUserInputAdvanced->OdtImpedanceWCK[3];
	}
	else if (strcmp(field, "EnWck2DqoTracking[0]") == 0) {
		return pUserInputAdvanced->EnWck2DqoTracking[0];
	}
	else if (strcmp(field, "EnWck2DqoTracking[1]") == 0) {
		return pUserInputAdvanced->EnWck2DqoTracking[1];
	}
	else if (strcmp(field, "EnWck2DqoTracking[2]") == 0) {
		return pUserInputAdvanced->EnWck2DqoTracking[2];
	}
	else if (strcmp(field, "EnWck2DqoTracking[3]") == 0) {
		return pUserInputAdvanced->EnWck2DqoTracking[3];
	}
	else if (strcmp(field, "AcInPipeEnOvr") == 0) {
		return pUserInputAdvanced->AcInPipeEnOvr;
	}
	else if (strcmp(field, "DtoEnable") == 0) {
		return pUserInputAdvanced->DtoEnable;
	}
	else if (strcmp(field, "CkDisVal[0]") == 0) {
		return pUserInputAdvanced->CkDisVal[0];
	}
	else if (strcmp(field, "CkDisVal[1]") == 0) {
		return pUserInputAdvanced->CkDisVal[1];
	}
	else if (strcmp(field, "CkDisVal[2]") == 0) {
		return pUserInputAdvanced->CkDisVal[2];
	}
	else if (strcmp(field, "CkDisVal[3]") == 0) {
		return pUserInputAdvanced->CkDisVal[3];
	}
	else if (strcmp(field, "DxRdPipeEnOvr") == 0) {
		return pUserInputAdvanced->DxRdPipeEnOvr;
	}
	else if (strcmp(field, "EnLpRxDqPowerDown") == 0) {
		return pUserInputAdvanced->EnLpRxDqPowerDown;
	}
	else if (strcmp(field, "TxSlewFallDq[0]") == 0) {
		return pUserInputAdvanced->TxSlewFallDq[0];
	}
	else if (strcmp(field, "TxSlewFallDq[1]") == 0) {
		return pUserInputAdvanced->TxSlewFallDq[1];
	}
	else if (strcmp(field, "TxSlewFallDq[2]") == 0) {
		return pUserInputAdvanced->TxSlewFallDq[2];
	}
	else if (strcmp(field, "TxSlewFallDq[3]") == 0) {
		return pUserInputAdvanced->TxSlewFallDq[3];
	}
	else if (strcmp(field, "TxImpedanceAc[0]") == 0) {
		return pUserInputAdvanced->TxImpedanceAc[0];
	}
	else if (strcmp(field, "TxImpedanceAc[1]") == 0) {
		return pUserInputAdvanced->TxImpedanceAc[1];
	}
	else if (strcmp(field, "TxImpedanceAc[2]") == 0) {
		return pUserInputAdvanced->TxImpedanceAc[2];
	}
	else if (strcmp(field, "TxImpedanceAc[3]") == 0) {
		return pUserInputAdvanced->TxImpedanceAc[3];
	}
	else if (strcmp(field, "CalInterval") == 0) {
		return pUserInputAdvanced->CalInterval;
	}
	else if (strcmp(field, "DisableRetraining") == 0) {
		return pUserInputAdvanced->DisableRetraining;
	}
	else if (strcmp(field, "TxImpedanceCk[0]") == 0) {
		return pUserInputAdvanced->TxImpedanceCk[0];
	}
	else if (strcmp(field, "TxImpedanceCk[1]") == 0) {
		return pUserInputAdvanced->TxImpedanceCk[1];
	}
	else if (strcmp(field, "TxImpedanceCk[2]") == 0) {
		return pUserInputAdvanced->TxImpedanceCk[2];
	}
	else if (strcmp(field, "TxImpedanceCk[3]") == 0) {
		return pUserInputAdvanced->TxImpedanceCk[3];
	}
	else if (strcmp(field, "DLEPKeyCode") == 0) {
		return pUserInputAdvanced->DLEPKeyCode;
	}
	else if (strcmp(field, "DxInPipeEn[0]") == 0) {
		return pUserInputAdvanced->DxInPipeEn[0];
	}
	else if (strcmp(field, "DxInPipeEn[1]") == 0) {
		return pUserInputAdvanced->DxInPipeEn[1];
	}
	else if (strcmp(field, "DxInPipeEn[2]") == 0) {
		return pUserInputAdvanced->DxInPipeEn[2];
	}
	else if (strcmp(field, "DxInPipeEn[3]") == 0) {
		return pUserInputAdvanced->DxInPipeEn[3];
	}
	else if (strcmp(field, "EnableSystemEcc") == 0) {
		return pUserInputAdvanced->EnableSystemEcc;
	}
	else if (strcmp(field, "PHYZCalPowerSaving") == 0) {
		return pUserInputAdvanced->PHYZCalPowerSaving;
	}
	else if (strcmp(field, "PhyMstrTrainInterval[0]") == 0) {
		return pUserInputAdvanced->PhyMstrTrainInterval[0];
	}
	else if (strcmp(field, "PhyMstrTrainInterval[1]") == 0) {
		return pUserInputAdvanced->PhyMstrTrainInterval[1];
	}
	else if (strcmp(field, "PhyMstrTrainInterval[2]") == 0) {
		return pUserInputAdvanced->PhyMstrTrainInterval[2];
	}
	else if (strcmp(field, "PhyMstrTrainInterval[3]") == 0) {
		return pUserInputAdvanced->PhyMstrTrainInterval[3];
	}
	else if (strcmp(field, "DxOutPipeEn[0]") == 0) {
		return pUserInputAdvanced->DxOutPipeEn[0];
	}
	else if (strcmp(field, "DxOutPipeEn[1]") == 0) {
		return pUserInputAdvanced->DxOutPipeEn[1];
	}
	else if (strcmp(field, "DxOutPipeEn[2]") == 0) {
		return pUserInputAdvanced->DxOutPipeEn[2];
	}
	else if (strcmp(field, "DxOutPipeEn[3]") == 0) {
		return pUserInputAdvanced->DxOutPipeEn[3];
	}
	else if (strcmp(field, "DisableFspOp") == 0) {
		return pUserInputAdvanced->DisableFspOp;
	}
	else if (strcmp(field, "DfiLpPipeClkDisable") == 0) {
		return pUserInputAdvanced->DfiLpPipeClkDisable;
	}
	else if (strcmp(field, "DisablePclkDca") == 0) {
		return pUserInputAdvanced->DisablePclkDca;
	}
	else if (strcmp(field, "RxDqsTrackingThreshold[0]") == 0) {
		return pUserInputAdvanced->RxDqsTrackingThreshold[0];
	}
	else if (strcmp(field, "RxDqsTrackingThreshold[1]") == 0) {
		return pUserInputAdvanced->RxDqsTrackingThreshold[1];
	}
	else if (strcmp(field, "RxDqsTrackingThreshold[2]") == 0) {
		return pUserInputAdvanced->RxDqsTrackingThreshold[2];
	}
	else if (strcmp(field, "RxDqsTrackingThreshold[3]") == 0) {
		return pUserInputAdvanced->RxDqsTrackingThreshold[3];
	}
	else if (strcmp(field, "TxImpedanceWCK[0]") == 0) {
		return pUserInputAdvanced->TxImpedanceWCK[0];
	}
	else if (strcmp(field, "TxImpedanceWCK[1]") == 0) {
		return pUserInputAdvanced->TxImpedanceWCK[1];
	}
	else if (strcmp(field, "TxImpedanceWCK[2]") == 0) {
		return pUserInputAdvanced->TxImpedanceWCK[2];
	}
	else if (strcmp(field, "TxImpedanceWCK[3]") == 0) {
		return pUserInputAdvanced->TxImpedanceWCK[3];
	}
	else if (strcmp(field, "OdtImpedanceDqs[0]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDqs[0];
	}
	else if (strcmp(field, "OdtImpedanceDqs[1]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDqs[1];
	}
	else if (strcmp(field, "OdtImpedanceDqs[2]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDqs[2];
	}
	else if (strcmp(field, "OdtImpedanceDqs[3]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDqs[3];
	}
	else if (strcmp(field, "AlertNPipeEn[0]") == 0) {
		return pUserInputAdvanced->AlertNPipeEn[0];
	}
	else if (strcmp(field, "AlertNPipeEn[1]") == 0) {
		return pUserInputAdvanced->AlertNPipeEn[1];
	}
	else if (strcmp(field, "AlertNPipeEn[2]") == 0) {
		return pUserInputAdvanced->AlertNPipeEn[2];
	}
	else if (strcmp(field, "AlertNPipeEn[3]") == 0) {
		return pUserInputAdvanced->AlertNPipeEn[3];
	}
	else if (strcmp(field, "SkipFlashCopy[0]") == 0) {
		return pUserInputAdvanced->SkipFlashCopy[0];
	}
	else if (strcmp(field, "SkipFlashCopy[1]") == 0) {
		return pUserInputAdvanced->SkipFlashCopy[1];
	}
	else if (strcmp(field, "SkipFlashCopy[2]") == 0) {
		return pUserInputAdvanced->SkipFlashCopy[2];
	}
	else if (strcmp(field, "SkipFlashCopy[3]") == 0) {
		return pUserInputAdvanced->SkipFlashCopy[3];
	}
	else if (strcmp(field, "DxRdPipeEn[0]") == 0) {
		return pUserInputAdvanced->DxRdPipeEn[0];
	}
	else if (strcmp(field, "DxRdPipeEn[1]") == 0) {
		return pUserInputAdvanced->DxRdPipeEn[1];
	}
	else if (strcmp(field, "DxRdPipeEn[2]") == 0) {
		return pUserInputAdvanced->DxRdPipeEn[2];
	}
	else if (strcmp(field, "DxRdPipeEn[3]") == 0) {
		return pUserInputAdvanced->DxRdPipeEn[3];
	}
	else if (strcmp(field, "Lp5xFwTinit3WaitTimex1000") == 0) {
		return pUserInputAdvanced->Lp5xFwTinit3WaitTimex1000;
	}
	else if (strcmp(field, "DisCheckAllUserInputsLegalVal") == 0) {
		return pUserInputAdvanced->DisCheckAllUserInputsLegalVal;
	}
	else if (strcmp(field, "SnoopWAEn[0]") == 0) {
		return pUserInputAdvanced->SnoopWAEn[0];
	}
	else if (strcmp(field, "SnoopWAEn[1]") == 0) {
		return pUserInputAdvanced->SnoopWAEn[1];
	}
	else if (strcmp(field, "SnoopWAEn[2]") == 0) {
		return pUserInputAdvanced->SnoopWAEn[2];
	}
	else if (strcmp(field, "SnoopWAEn[3]") == 0) {
		return pUserInputAdvanced->SnoopWAEn[3];
	}
	else if (strcmp(field, "ACDlyScaleGating") == 0) {
		return pUserInputAdvanced->ACDlyScaleGating;
	}
	else if (strcmp(field, "TxSlewRiseDq[0]") == 0) {
		return pUserInputAdvanced->TxSlewRiseDq[0];
	}
	else if (strcmp(field, "TxSlewRiseDq[1]") == 0) {
		return pUserInputAdvanced->TxSlewRiseDq[1];
	}
	else if (strcmp(field, "TxSlewRiseDq[2]") == 0) {
		return pUserInputAdvanced->TxSlewRiseDq[2];
	}
	else if (strcmp(field, "TxSlewRiseDq[3]") == 0) {
		return pUserInputAdvanced->TxSlewRiseDq[3];
	}
	else if (strcmp(field, "IMEMLoadPerfEn") == 0) {
		return pUserInputAdvanced->IMEMLoadPerfEn;
	}
	else if (strcmp(field, "AcInPipeEn[0]") == 0) {
		return pUserInputAdvanced->AcInPipeEn[0];
	}
	else if (strcmp(field, "AcInPipeEn[1]") == 0) {
		return pUserInputAdvanced->AcInPipeEn[1];
	}
	else if (strcmp(field, "AcInPipeEn[2]") == 0) {
		return pUserInputAdvanced->AcInPipeEn[2];
	}
	else if (strcmp(field, "AcInPipeEn[3]") == 0) {
		return pUserInputAdvanced->AcInPipeEn[3];
	}
	else if (strcmp(field, "DisCheckImpTxRx[0]") == 0) {
		return pUserInputAdvanced->DisCheckImpTxRx[0];
	}
	else if (strcmp(field, "DisCheckImpTxRx[1]") == 0) {
		return pUserInputAdvanced->DisCheckImpTxRx[1];
	}
	else if (strcmp(field, "DisCheckImpTxRx[2]") == 0) {
		return pUserInputAdvanced->DisCheckImpTxRx[2];
	}
	else if (strcmp(field, "DisCheckImpTxRx[3]") == 0) {
		return pUserInputAdvanced->DisCheckImpTxRx[3];
	}
	else if (strcmp(field, "AcQuarterDataRate") == 0) {
		return pUserInputAdvanced->AcQuarterDataRate;
	}
	else if (strcmp(field, "DisCheckDvfsqDramOdt[0]") == 0) {
		return pUserInputAdvanced->DisCheckDvfsqDramOdt[0];
	}
	else if (strcmp(field, "DisCheckDvfsqDramOdt[1]") == 0) {
		return pUserInputAdvanced->DisCheckDvfsqDramOdt[1];
	}
	else if (strcmp(field, "DisCheckDvfsqDramOdt[2]") == 0) {
		return pUserInputAdvanced->DisCheckDvfsqDramOdt[2];
	}
	else if (strcmp(field, "DisCheckDvfsqDramOdt[3]") == 0) {
		return pUserInputAdvanced->DisCheckDvfsqDramOdt[3];
	}
	else if (strcmp(field, "ZcalClkDiv[0]") == 0) {
		return pUserInputAdvanced->ZcalClkDiv[0];
	}
	else if (strcmp(field, "ZcalClkDiv[1]") == 0) {
		return pUserInputAdvanced->ZcalClkDiv[1];
	}
	else if (strcmp(field, "ZcalClkDiv[2]") == 0) {
		return pUserInputAdvanced->ZcalClkDiv[2];
	}
	else if (strcmp(field, "ZcalClkDiv[3]") == 0) {
		return pUserInputAdvanced->ZcalClkDiv[3];
	}
	else if (strcmp(field, "OdtImpedanceCa[0]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCa[0];
	}
	else if (strcmp(field, "OdtImpedanceCa[1]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCa[1];
	}
	else if (strcmp(field, "OdtImpedanceCa[2]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCa[2];
	}
	else if (strcmp(field, "OdtImpedanceCa[3]") == 0) {
		return pUserInputAdvanced->OdtImpedanceCa[3];
	}
	else if (strcmp(field, "RxBiasCurrentControlWck[0]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlWck[0];
	}
	else if (strcmp(field, "RxBiasCurrentControlWck[1]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlWck[1];
	}
	else if (strcmp(field, "RxBiasCurrentControlWck[2]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlWck[2];
	}
	else if (strcmp(field, "RxBiasCurrentControlWck[3]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlWck[3];
	}
	else if (strcmp(field, "PhyMstrMaxReqToAck[0]") == 0) {
		return pUserInputAdvanced->PhyMstrMaxReqToAck[0];
	}
	else if (strcmp(field, "PhyMstrMaxReqToAck[1]") == 0) {
		return pUserInputAdvanced->PhyMstrMaxReqToAck[1];
	}
	else if (strcmp(field, "PhyMstrMaxReqToAck[2]") == 0) {
		return pUserInputAdvanced->PhyMstrMaxReqToAck[2];
	}
	else if (strcmp(field, "PhyMstrMaxReqToAck[3]") == 0) {
		return pUserInputAdvanced->PhyMstrMaxReqToAck[3];
	}
	else if (strcmp(field, "TxSlewRiseCK[0]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCK[0];
	}
	else if (strcmp(field, "TxSlewRiseCK[1]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCK[1];
	}
	else if (strcmp(field, "TxSlewRiseCK[2]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCK[2];
	}
	else if (strcmp(field, "TxSlewRiseCK[3]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCK[3];
	}
	else if (strcmp(field, "DramByteSwap") == 0) {
		return pUserInputAdvanced->DramByteSwap;
	}
	else if (strcmp(field, "DisZCalOnDataRate") == 0) {
		return pUserInputAdvanced->DisZCalOnDataRate;
	}
	else if (strcmp(field, "RxClkTrackEn[0]") == 0) {
		return pUserInputAdvanced->RxClkTrackEn[0];
	}
	else if (strcmp(field, "RxClkTrackEn[1]") == 0) {
		return pUserInputAdvanced->RxClkTrackEn[1];
	}
	else if (strcmp(field, "RxClkTrackEn[2]") == 0) {
		return pUserInputAdvanced->RxClkTrackEn[2];
	}
	else if (strcmp(field, "RxClkTrackEn[3]") == 0) {
		return pUserInputAdvanced->RxClkTrackEn[3];
	}
	else if (strcmp(field, "OdtImpedanceDq[0]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDq[0];
	}
	else if (strcmp(field, "OdtImpedanceDq[1]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDq[1];
	}
	else if (strcmp(field, "OdtImpedanceDq[2]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDq[2];
	}
	else if (strcmp(field, "OdtImpedanceDq[3]") == 0) {
		return pUserInputAdvanced->OdtImpedanceDq[3];
	}
	else if (strcmp(field, "CoreVddScalingMode[0]") == 0) {
		return pUserInputAdvanced->CoreVddScalingMode[0];
	}
	else if (strcmp(field, "CoreVddScalingMode[1]") == 0) {
		return pUserInputAdvanced->CoreVddScalingMode[1];
	}
	else if (strcmp(field, "CoreVddScalingMode[2]") == 0) {
		return pUserInputAdvanced->CoreVddScalingMode[2];
	}
	else if (strcmp(field, "CoreVddScalingMode[3]") == 0) {
		return pUserInputAdvanced->CoreVddScalingMode[3];
	}
	else if (strcmp(field, "RxDFECtrlDq[0]") == 0) {
		return pUserInputAdvanced->RxDFECtrlDq[0];
	}
	else if (strcmp(field, "RxDFECtrlDq[1]") == 0) {
		return pUserInputAdvanced->RxDFECtrlDq[1];
	}
	else if (strcmp(field, "RxDFECtrlDq[2]") == 0) {
		return pUserInputAdvanced->RxDFECtrlDq[2];
	}
	else if (strcmp(field, "RxDFECtrlDq[3]") == 0) {
		return pUserInputAdvanced->RxDFECtrlDq[3];
	}
	else if (strcmp(field, "DxInPipeEnOvr") == 0) {
		return pUserInputAdvanced->DxInPipeEnOvr;
	}
	else if (strcmp(field, "TxSlewFallCS[0]") == 0) {
		return pUserInputAdvanced->TxSlewFallCS[0];
	}
	else if (strcmp(field, "TxSlewFallCS[1]") == 0) {
		return pUserInputAdvanced->TxSlewFallCS[1];
	}
	else if (strcmp(field, "TxSlewFallCS[2]") == 0) {
		return pUserInputAdvanced->TxSlewFallCS[2];
	}
	else if (strcmp(field, "TxSlewFallCS[3]") == 0) {
		return pUserInputAdvanced->TxSlewFallCS[3];
	}
	else if (strcmp(field, "AlertNPipeEnOvr") == 0) {
		return pUserInputAdvanced->AlertNPipeEnOvr;
	}
	else if (strcmp(field, "SkipPwrDnInRetrain") == 0) {
		return pUserInputAdvanced->SkipPwrDnInRetrain;
	}
	else if (strcmp(field, "TxSlewFallCA[0]") == 0) {
		return pUserInputAdvanced->TxSlewFallCA[0];
	}
	else if (strcmp(field, "TxSlewFallCA[1]") == 0) {
		return pUserInputAdvanced->TxSlewFallCA[1];
	}
	else if (strcmp(field, "TxSlewFallCA[2]") == 0) {
		return pUserInputAdvanced->TxSlewFallCA[2];
	}
	else if (strcmp(field, "TxSlewFallCA[3]") == 0) {
		return pUserInputAdvanced->TxSlewFallCA[3];
	}
	else if (strcmp(field, "DqsOscRunTimeSel[0]") == 0) {
		return pUserInputAdvanced->DqsOscRunTimeSel[0];
	}
	else if (strcmp(field, "DqsOscRunTimeSel[1]") == 0) {
		return pUserInputAdvanced->DqsOscRunTimeSel[1];
	}
	else if (strcmp(field, "DqsOscRunTimeSel[2]") == 0) {
		return pUserInputAdvanced->DqsOscRunTimeSel[2];
	}
	else if (strcmp(field, "DqsOscRunTimeSel[3]") == 0) {
		return pUserInputAdvanced->DqsOscRunTimeSel[3];
	}
	else if (strcmp(field, "RxBiasCurrentControlRxReplica[0]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlRxReplica[0];
	}
	else if (strcmp(field, "RxBiasCurrentControlRxReplica[1]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlRxReplica[1];
	}
	else if (strcmp(field, "RxBiasCurrentControlRxReplica[2]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlRxReplica[2];
	}
	else if (strcmp(field, "RxBiasCurrentControlRxReplica[3]") == 0) {
		return pUserInputAdvanced->RxBiasCurrentControlRxReplica[3];
	}
	else if (strcmp(field, "Lp3DramState[0]") == 0) {
		return pUserInputAdvanced->Lp3DramState[0];
	}
	else if (strcmp(field, "Lp3DramState[1]") == 0) {
		return pUserInputAdvanced->Lp3DramState[1];
	}
	else if (strcmp(field, "Lp3DramState[2]") == 0) {
		return pUserInputAdvanced->Lp3DramState[2];
	}
	else if (strcmp(field, "Lp3DramState[3]") == 0) {
		return pUserInputAdvanced->Lp3DramState[3];
	}
	else if (strcmp(field, "TxSlewRiseCS[0]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCS[0];
	}
	else if (strcmp(field, "TxSlewRiseCS[1]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCS[1];
	}
	else if (strcmp(field, "TxSlewRiseCS[2]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCS[2];
	}
	else if (strcmp(field, "TxSlewRiseCS[3]") == 0) {
		return pUserInputAdvanced->TxSlewRiseCS[3];
	}
	else if (strcmp(field, "UseSnpsController") == 0) {
		return pUserInputAdvanced->UseSnpsController;
	}
	else if (strcmp(field, "DisRxClkCLcdl[0]") == 0) {
		return pUserInputAdvanced->DisRxClkCLcdl[0];
	}
	else if (strcmp(field, "DisRxClkCLcdl[1]") == 0) {
		return pUserInputAdvanced->DisRxClkCLcdl[1];
	}
	else if (strcmp(field, "DisRxClkCLcdl[2]") == 0) {
		return pUserInputAdvanced->DisRxClkCLcdl[2];
	}
	else if (strcmp(field, "DisRxClkCLcdl[3]") == 0) {
		return pUserInputAdvanced->DisRxClkCLcdl[3];
	}
	else if (strcmp(field, "TxImpedanceDq[0]") == 0) {
		return pUserInputAdvanced->TxImpedanceDq[0];
	}
	else if (strcmp(field, "TxImpedanceDq[1]") == 0) {
		return pUserInputAdvanced->TxImpedanceDq[1];
	}
	else if (strcmp(field, "TxImpedanceDq[2]") == 0) {
		return pUserInputAdvanced->TxImpedanceDq[2];
	}
	else if (strcmp(field, "TxImpedanceDq[3]") == 0) {
		return pUserInputAdvanced->TxImpedanceDq[3];
	}
	else if (strcmp(field, "DisablePhyUpdate") == 0) {
		return pUserInputAdvanced->DisablePhyUpdate;
	}
	else if (strcmp(field, "HalfTxCalCode") == 0) {
		return pUserInputAdvanced->HalfTxCalCode;
	}
	else if (strcmp(field, "DxOutPipeEnOvr") == 0) {
		return pUserInputAdvanced->DxOutPipeEnOvr;
	}
	else if (strcmp(field, "RetrainMode[0]") == 0) {
		return pUserInputAdvanced->RetrainMode[0];
	}
	else if (strcmp(field, "RetrainMode[1]") == 0) {
		return pUserInputAdvanced->RetrainMode[1];
	}
	else if (strcmp(field, "RetrainMode[2]") == 0) {
		return pUserInputAdvanced->RetrainMode[2];
	}
	else if (strcmp(field, "RetrainMode[3]") == 0) {
		return pUserInputAdvanced->RetrainMode[3];
	}
	else if (strcmp(field, "DfiLoopbackEn") == 0) {
		return pUserInputAdvanced->DfiLoopbackEn;
	}
	else if (strcmp(field, "DisablePmuEcc") == 0) {
		return pUserInputAdvanced->DisablePmuEcc;
	}
	else if (strcmp(field, "TxImpedanceDqs[0]") == 0) {
		return pUserInputAdvanced->TxImpedanceDqs[0];
	}
	else if (strcmp(field, "TxImpedanceDqs[1]") == 0) {
		return pUserInputAdvanced->TxImpedanceDqs[1];
	}
	else if (strcmp(field, "TxImpedanceDqs[2]") == 0) {
		return pUserInputAdvanced->TxImpedanceDqs[2];
	}
	else if (strcmp(field, "TxImpedanceDqs[3]") == 0) {
		return pUserInputAdvanced->TxImpedanceDqs[3];
	}
	else if (strcmp(field, "TrainSequenceCtrl[0]") == 0) {
		return pUserInputAdvanced->TrainSequenceCtrl[0];
	}
	else if (strcmp(field, "TrainSequenceCtrl[1]") == 0) {
		return pUserInputAdvanced->TrainSequenceCtrl[1];
	}
	else if (strcmp(field, "TrainSequenceCtrl[2]") == 0) {
		return pUserInputAdvanced->TrainSequenceCtrl[2];
	}
	else if (strcmp(field, "TrainSequenceCtrl[3]") == 0) {
		return pUserInputAdvanced->TrainSequenceCtrl[3];
	}
	else if (strcmp(field, "PmuClockDiv[0]") == 0) {
		return pUserInputAdvanced->PmuClockDiv[0];
	}
	else if (strcmp(field, "PmuClockDiv[1]") == 0) {
		return pUserInputAdvanced->PmuClockDiv[1];
	}
	else if (strcmp(field, "PmuClockDiv[2]") == 0) {
		return pUserInputAdvanced->PmuClockDiv[2];
	}
	else if (strcmp(field, "PmuClockDiv[3]") == 0) {
		return pUserInputAdvanced->PmuClockDiv[3];
	}
	else if (strcmp(field, "DqsSampNegRxEnSense[0]") == 0) {
		return pUserInputAdvanced->DqsSampNegRxEnSense[0];
	}
	else if (strcmp(field, "DqsSampNegRxEnSense[1]") == 0) {
		return pUserInputAdvanced->DqsSampNegRxEnSense[1];
	}
	else if (strcmp(field, "DqsSampNegRxEnSense[2]") == 0) {
		return pUserInputAdvanced->DqsSampNegRxEnSense[2];
	}
	else if (strcmp(field, "DqsSampNegRxEnSense[3]") == 0) {
		return pUserInputAdvanced->DqsSampNegRxEnSense[3];
	}
	else if (strcmp(field, "TxImpedanceCsCke") == 0) {
		return pUserInputAdvanced->TxImpedanceCsCke;
	}
	else if (strcmp(field, "LcdlRxInsertionDelay") == 0) {
		return pUserInputSim->LcdlRxInsertionDelay;
	}
	else if (strcmp(field, "tWCK2DQO") == 0) {
		return pUserInputSim->tWCK2DQO;
	}
	else if (strcmp(field, "tWCK2DQI") == 0) {
		return pUserInputSim->tWCK2DQI;
	}
	else if (strcmp(field, "tWCK2CK") == 0) {
		return pUserInputSim->tWCK2CK;
	}
	else if (strcmp(field, "LcdlTxInsertionDelay") == 0) {
		return pUserInputSim->LcdlTxInsertionDelay;
	}
	else if (strcmp(field, "PHY_tDQS2DQ") == 0) {
		return pUserInputSim->PHY_tDQS2DQ;
	}
	else if (strcmp(field, "RxEnDlyOffset_Reserved") == 0) {
		return pUserInputSim->RxEnDlyOffset_Reserved;
	}
	else if (strcmp(field, "LcdlNumSteps") == 0) {
		return pUserInputSim->LcdlNumSteps;
	}
	else if (strcmp(field, "LcdlStepSizex10") == 0) {
		return pUserInputSim->LcdlStepSizex10;
	}
	else {
		dwc_ddrphy_phyinit_assert(0, " [%s] Invalid field : %s\n", __func__, field);
	    return -1;
	}
}

/** @} */
