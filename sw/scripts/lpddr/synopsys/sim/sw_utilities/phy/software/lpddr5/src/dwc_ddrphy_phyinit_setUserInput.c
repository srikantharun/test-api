/** \file
 * \brief API used to change PhyInit fields.
 * \addtogroup SrcFunc
 * @{
 */

#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** @brief API to get the userInput decoded enum string name
 *
 *  @param[in] field A string representing the field to be programed. bracket
 *  notation can be used to set array fields. example  string: "PllBypass[0]"
 *  set the field UserInputBasic.PllBypass[0].
 *
 *  @return char * Decode string value of enum
 *  data structures.
 */

extern char *dwc_ddrphy_phyinit_setUserInput_enumDecode(userInputFields field);
// coverity[misra_c_2012_rule_5_1_violation]
char *dwc_ddrphy_phyinit_setUserInput_enumDecode(userInputFields field)
{
	static char *field_enum_decode[] = {
		"NumAchnActive",
"firstTrainedPState",
"DataRateMbps[0]",
"DataRateMbps[1]",
"DataRateMbps[2]",
"DataRateMbps[3]",
"psExecOrder[0]",
"psExecOrder[1]",
"psExecOrder[2]",
"psExecOrder[3]",
"NumDbyteActive",
"enableBits[0]",
"enableBits[1]",
"enableBits[2]",
"NumDxOutPipeEn[0]",
"NumDxOutPipeEn[1]",
"NumDxOutPipeEn[2]",
"NumDxOutPipeEn[3]",
"NumDxInPipeEn[0]",
"NumDxInPipeEn[1]",
"NumDxInPipeEn[2]",
"NumDxInPipeEn[3]",
"NumMiscPipeEn[0]",
"NumMiscPipeEn[1]",
"NumMiscPipeEn[2]",
"NumMiscPipeEn[3]",
"NumDbyte",
"skip_train",
"initCtrl",
"TG_active[0]",
"TG_active[1]",
"TG_active[2]",
"TG_active[3]",
"NumAcInPipeEn[0]",
"NumAcInPipeEn[1]",
"NumAcInPipeEn[2]",
"NumAcInPipeEn[3]",
"UcclkFull[0]",
"UcclkFull[1]",
"UcclkFull[2]",
"UcclkFull[3]",
"DfiFreq[0]",
"DfiFreq[1]",
"DfiFreq[2]",
"DfiFreq[3]",
"Train2D",
"tck_ps[0]",
"tck_ps[1]",
"tck_ps[2]",
"tck_ps[3]",
"NumAlertNPipeEn[0]",
"NumAlertNPipeEn[1]",
"NumAlertNPipeEn[2]",
"NumAlertNPipeEn[3]",
"pubRev",
"debug",
"curD",
"lastTrainedPState",
"RetEn",
"curPState",
"CalImpedanceCurrentAdjustment",
"CalOnce",
"DMEMLoadPerfEn",
"TxSlewRiseCA[0]",
"TxSlewRiseCA[1]",
"TxSlewRiseCA[2]",
"TxSlewRiseCA[3]",
"RxGainCtrl",
"DramStateChangeEn",
"TxSlewFallCK[0]",
"TxSlewFallCK[1]",
"TxSlewFallCK[2]",
"TxSlewFallCK[3]",
"OdtImpedanceCk[0]",
"OdtImpedanceCk[1]",
"OdtImpedanceCk[2]",
"OdtImpedanceCk[3]",
"Lp5xDeassertDramReset",
"OdtImpedanceWCK[0]",
"OdtImpedanceWCK[1]",
"OdtImpedanceWCK[2]",
"OdtImpedanceWCK[3]",
"EnWck2DqoTracking[0]",
"EnWck2DqoTracking[1]",
"EnWck2DqoTracking[2]",
"EnWck2DqoTracking[3]",
"AcInPipeEnOvr",
"DtoEnable",
"CkDisVal[0]",
"CkDisVal[1]",
"CkDisVal[2]",
"CkDisVal[3]",
"DxRdPipeEnOvr",
"EnLpRxDqPowerDown",
"TxSlewFallDq[0]",
"TxSlewFallDq[1]",
"TxSlewFallDq[2]",
"TxSlewFallDq[3]",
"TxImpedanceAc[0]",
"TxImpedanceAc[1]",
"TxImpedanceAc[2]",
"TxImpedanceAc[3]",
"CalInterval",
"DisableRetraining",
"TxImpedanceCk[0]",
"TxImpedanceCk[1]",
"TxImpedanceCk[2]",
"TxImpedanceCk[3]",
"DLEPKeyCode",
"DxInPipeEn[0]",
"DxInPipeEn[1]",
"DxInPipeEn[2]",
"DxInPipeEn[3]",
"EnableSystemEcc",
"PHYZCalPowerSaving",
"PhyMstrTrainInterval[0]",
"PhyMstrTrainInterval[1]",
"PhyMstrTrainInterval[2]",
"PhyMstrTrainInterval[3]",
"DxOutPipeEn[0]",
"DxOutPipeEn[1]",
"DxOutPipeEn[2]",
"DxOutPipeEn[3]",
"DisableFspOp",
"DfiLpPipeClkDisable",
"DisablePclkDca",
"RxDqsTrackingThreshold[0]",
"RxDqsTrackingThreshold[1]",
"RxDqsTrackingThreshold[2]",
"RxDqsTrackingThreshold[3]",
"TxImpedanceWCK[0]",
"TxImpedanceWCK[1]",
"TxImpedanceWCK[2]",
"TxImpedanceWCK[3]",
"OdtImpedanceDqs[0]",
"OdtImpedanceDqs[1]",
"OdtImpedanceDqs[2]",
"OdtImpedanceDqs[3]",
"AlertNPipeEn[0]",
"AlertNPipeEn[1]",
"AlertNPipeEn[2]",
"AlertNPipeEn[3]",
"SkipFlashCopy[0]",
"SkipFlashCopy[1]",
"SkipFlashCopy[2]",
"SkipFlashCopy[3]",
"DxRdPipeEn[0]",
"DxRdPipeEn[1]",
"DxRdPipeEn[2]",
"DxRdPipeEn[3]",
"Lp5xFwTinit3WaitTimex1000",
"DisCheckAllUserInputsLegalVal",
"SnoopWAEn[0]",
"SnoopWAEn[1]",
"SnoopWAEn[2]",
"SnoopWAEn[3]",
"ACDlyScaleGating",
"TxSlewRiseDq[0]",
"TxSlewRiseDq[1]",
"TxSlewRiseDq[2]",
"TxSlewRiseDq[3]",
"IMEMLoadPerfEn",
"AcInPipeEn[0]",
"AcInPipeEn[1]",
"AcInPipeEn[2]",
"AcInPipeEn[3]",
"DisCheckImpTxRx[0]",
"DisCheckImpTxRx[1]",
"DisCheckImpTxRx[2]",
"DisCheckImpTxRx[3]",
"AcQuarterDataRate",
"DisCheckDvfsqDramOdt[0]",
"DisCheckDvfsqDramOdt[1]",
"DisCheckDvfsqDramOdt[2]",
"DisCheckDvfsqDramOdt[3]",
"ZcalClkDiv[0]",
"ZcalClkDiv[1]",
"ZcalClkDiv[2]",
"ZcalClkDiv[3]",
"OdtImpedanceCa[0]",
"OdtImpedanceCa[1]",
"OdtImpedanceCa[2]",
"OdtImpedanceCa[3]",
"RxBiasCurrentControlWck[0]",
"RxBiasCurrentControlWck[1]",
"RxBiasCurrentControlWck[2]",
"RxBiasCurrentControlWck[3]",
"PhyMstrMaxReqToAck[0]",
"PhyMstrMaxReqToAck[1]",
"PhyMstrMaxReqToAck[2]",
"PhyMstrMaxReqToAck[3]",
"TxSlewRiseCK[0]",
"TxSlewRiseCK[1]",
"TxSlewRiseCK[2]",
"TxSlewRiseCK[3]",
"DramByteSwap",
"DisZCalOnDataRate",
"RxClkTrackEn[0]",
"RxClkTrackEn[1]",
"RxClkTrackEn[2]",
"RxClkTrackEn[3]",
"OdtImpedanceDq[0]",
"OdtImpedanceDq[1]",
"OdtImpedanceDq[2]",
"OdtImpedanceDq[3]",
"CoreVddScalingMode[0]",
"CoreVddScalingMode[1]",
"CoreVddScalingMode[2]",
"CoreVddScalingMode[3]",
"RxDFECtrlDq[0]",
"RxDFECtrlDq[1]",
"RxDFECtrlDq[2]",
"RxDFECtrlDq[3]",
"DxInPipeEnOvr",
"TxSlewFallCS[0]",
"TxSlewFallCS[1]",
"TxSlewFallCS[2]",
"TxSlewFallCS[3]",
"AlertNPipeEnOvr",
"SkipPwrDnInRetrain",
"TxSlewFallCA[0]",
"TxSlewFallCA[1]",
"TxSlewFallCA[2]",
"TxSlewFallCA[3]",
"DqsOscRunTimeSel[0]",
"DqsOscRunTimeSel[1]",
"DqsOscRunTimeSel[2]",
"DqsOscRunTimeSel[3]",
"RxBiasCurrentControlRxReplica[0]",
"RxBiasCurrentControlRxReplica[1]",
"RxBiasCurrentControlRxReplica[2]",
"RxBiasCurrentControlRxReplica[3]",
"Lp3DramState[0]",
"Lp3DramState[1]",
"Lp3DramState[2]",
"Lp3DramState[3]",
"TxSlewRiseCS[0]",
"TxSlewRiseCS[1]",
"TxSlewRiseCS[2]",
"TxSlewRiseCS[3]",
"UseSnpsController",
"DisRxClkCLcdl[0]",
"DisRxClkCLcdl[1]",
"DisRxClkCLcdl[2]",
"DisRxClkCLcdl[3]",
"TxImpedanceDq[0]",
"TxImpedanceDq[1]",
"TxImpedanceDq[2]",
"TxImpedanceDq[3]",
"DisablePhyUpdate",
"HalfTxCalCode",
"DxOutPipeEnOvr",
"RetrainMode[0]",
"RetrainMode[1]",
"RetrainMode[2]",
"RetrainMode[3]",
"DfiLoopbackEn",
"DisablePmuEcc",
"TxImpedanceDqs[0]",
"TxImpedanceDqs[1]",
"TxImpedanceDqs[2]",
"TxImpedanceDqs[3]",
"TrainSequenceCtrl[0]",
"TrainSequenceCtrl[1]",
"TrainSequenceCtrl[2]",
"TrainSequenceCtrl[3]",
"PmuClockDiv[0]",
"PmuClockDiv[1]",
"PmuClockDiv[2]",
"PmuClockDiv[3]",
"DqsSampNegRxEnSense[0]",
"DqsSampNegRxEnSense[1]",
"DqsSampNegRxEnSense[2]",
"DqsSampNegRxEnSense[3]",
"TxImpedanceCsCke",
"NumPStates",
"NumRank_dfi0",
"HardMacroVer",
"NumCh",
"DimmType",
"Lp5xMode",
"DramType",
"DfiFreqRatio[0]",
"DfiFreqRatio[1]",
"DfiFreqRatio[2]",
"DfiFreqRatio[3]",
"FirstPState",
"NumActiveDbyteDfi1",
"NumRank",
"DramDataWidth",
"CfgPStates",
"PclkPtrInitValOvr",
"Frequency[0]",
"Frequency[1]",
"Frequency[2]",
"Frequency[3]",
"PllBypass[0]",
"PllBypass[1]",
"PllBypass[2]",
"PllBypass[3]",
"NumRank_dfi1",
"NumDbytesPerCh",
"PclkPtrInitVal[0]",
"PclkPtrInitVal[1]",
"PclkPtrInitVal[2]",
"PclkPtrInitVal[3]",
"MaxNumZQ",
"NumActiveDbyteDfi0",
"LcdlRxInsertionDelay",
"tWCK2DQO",
"tWCK2DQI",
"tWCK2CK",
"LcdlTxInsertionDelay",
"PHY_tDQS2DQ",
"RxEnDlyOffset_Reserved",
"LcdlNumSteps",
"LcdlStepSizex10",
	};

	if (field < 0 || field >= 317) {
		return "Enum out of range";
	}
	else {
		return field_enum_decode[field];
	}
}


/** @brief API to set the userInput enum value
 *
 *  @param[in]   phyctx PhyInit configuration context
 *
 *  @param[in]   field  A string representing the field to be programed. bracket
 *  notation can be used to set array fields. example  string: "PllBypass[0]"
 *  set the field UserInputBasic.PllBypass[0].
 *
 *  @param[in]   value  Value to be set on the field.
 *
 *  @return 0 on success. -1 when field does not match fields in any of PhyInit
 *  data structures.
 */
// coverity[misra_c_2012_rule_5_1_violation]
int dwc_ddrphy_phyinit_setUserInput_enum(phyinit_config_t *phyctx, userInputFields field, int value)
{
	user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
	user_input_sim_t *pUserInputSim = &phyctx->userInputSim;
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	int result = 0;

	switch (field) {
	case 0:
		pRuntimeConfig->NumAchnActive = value;
		break;
	case 1:
		pRuntimeConfig->firstTrainedPState = value;
		break;
	case 2:
		pRuntimeConfig->DataRateMbps[0] = value;
		break;
	case 3:
		pRuntimeConfig->DataRateMbps[1] = value;
		break;
	case 4:
		pRuntimeConfig->DataRateMbps[2] = value;
		break;
	case 5:
		pRuntimeConfig->DataRateMbps[3] = value;
		break;
	case 6:
		pRuntimeConfig->psExecOrder[0] = value;
		break;
	case 7:
		pRuntimeConfig->psExecOrder[1] = value;
		break;
	case 8:
		pRuntimeConfig->psExecOrder[2] = value;
		break;
	case 9:
		pRuntimeConfig->psExecOrder[3] = value;
		break;
	case 10:
		pRuntimeConfig->NumDbyteActive = value;
		break;
	case 11:
		pRuntimeConfig->enableBits[0] = value;
		break;
	case 12:
		pRuntimeConfig->enableBits[1] = value;
		break;
	case 13:
		pRuntimeConfig->enableBits[2] = value;
		break;
	case 14:
		pRuntimeConfig->NumDxOutPipeEn[0] = value;
		break;
	case 15:
		pRuntimeConfig->NumDxOutPipeEn[1] = value;
		break;
	case 16:
		pRuntimeConfig->NumDxOutPipeEn[2] = value;
		break;
	case 17:
		pRuntimeConfig->NumDxOutPipeEn[3] = value;
		break;
	case 18:
		pRuntimeConfig->NumDxInPipeEn[0] = value;
		break;
	case 19:
		pRuntimeConfig->NumDxInPipeEn[1] = value;
		break;
	case 20:
		pRuntimeConfig->NumDxInPipeEn[2] = value;
		break;
	case 21:
		pRuntimeConfig->NumDxInPipeEn[3] = value;
		break;
	case 22:
		pRuntimeConfig->NumMiscPipeEn[0] = value;
		break;
	case 23:
		pRuntimeConfig->NumMiscPipeEn[1] = value;
		break;
	case 24:
		pRuntimeConfig->NumMiscPipeEn[2] = value;
		break;
	case 25:
		pRuntimeConfig->NumMiscPipeEn[3] = value;
		break;
	case 26:
		pRuntimeConfig->NumDbyte = value;
		break;
	case 27:
		pRuntimeConfig->skip_train = value;
		break;
	case 28:
		pRuntimeConfig->initCtrl = value;
		break;
	case 29:
		pRuntimeConfig->TG_active[0] = value;
		break;
	case 30:
		pRuntimeConfig->TG_active[1] = value;
		break;
	case 31:
		pRuntimeConfig->TG_active[2] = value;
		break;
	case 32:
		pRuntimeConfig->TG_active[3] = value;
		break;
	case 33:
		pRuntimeConfig->NumAcInPipeEn[0] = value;
		break;
	case 34:
		pRuntimeConfig->NumAcInPipeEn[1] = value;
		break;
	case 35:
		pRuntimeConfig->NumAcInPipeEn[2] = value;
		break;
	case 36:
		pRuntimeConfig->NumAcInPipeEn[3] = value;
		break;
	case 37:
		pRuntimeConfig->UcclkFull[0] = value;
		break;
	case 38:
		pRuntimeConfig->UcclkFull[1] = value;
		break;
	case 39:
		pRuntimeConfig->UcclkFull[2] = value;
		break;
	case 40:
		pRuntimeConfig->UcclkFull[3] = value;
		break;
	case 41:
		pRuntimeConfig->DfiFreq[0] = value;
		break;
	case 42:
		pRuntimeConfig->DfiFreq[1] = value;
		break;
	case 43:
		pRuntimeConfig->DfiFreq[2] = value;
		break;
	case 44:
		pRuntimeConfig->DfiFreq[3] = value;
		break;
	case 45:
		pRuntimeConfig->Train2D = value;
		break;
	case 46:
		pRuntimeConfig->tck_ps[0] = value;
		break;
	case 47:
		pRuntimeConfig->tck_ps[1] = value;
		break;
	case 48:
		pRuntimeConfig->tck_ps[2] = value;
		break;
	case 49:
		pRuntimeConfig->tck_ps[3] = value;
		break;
	case 50:
		pRuntimeConfig->NumAlertNPipeEn[0] = value;
		break;
	case 51:
		pRuntimeConfig->NumAlertNPipeEn[1] = value;
		break;
	case 52:
		pRuntimeConfig->NumAlertNPipeEn[2] = value;
		break;
	case 53:
		pRuntimeConfig->NumAlertNPipeEn[3] = value;
		break;
	case 54:
		pRuntimeConfig->pubRev = value;
		break;
	case 55:
		pRuntimeConfig->debug = value;
		break;
	case 56:
		pRuntimeConfig->curD = value;
		break;
	case 57:
		pRuntimeConfig->lastTrainedPState = value;
		break;
	case 58:
		pRuntimeConfig->RetEn = value;
		break;
	case 59:
		pRuntimeConfig->curPState = value;
		break;
	case 60:
		pUserInputAdvanced->CalImpedanceCurrentAdjustment = value;
		break;
	case 61:
		pUserInputAdvanced->CalOnce = value;
		break;
	case 62:
		pUserInputAdvanced->DMEMLoadPerfEn = value;
		break;
	case 63:
		pUserInputAdvanced->TxSlewRiseCA[0] = value;
		break;
	case 64:
		pUserInputAdvanced->TxSlewRiseCA[1] = value;
		break;
	case 65:
		pUserInputAdvanced->TxSlewRiseCA[2] = value;
		break;
	case 66:
		pUserInputAdvanced->TxSlewRiseCA[3] = value;
		break;
	case 67:
		pUserInputAdvanced->RxGainCtrl = value;
		break;
	case 68:
		pUserInputAdvanced->DramStateChangeEn = value;
		break;
	case 69:
		pUserInputAdvanced->TxSlewFallCK[0] = value;
		break;
	case 70:
		pUserInputAdvanced->TxSlewFallCK[1] = value;
		break;
	case 71:
		pUserInputAdvanced->TxSlewFallCK[2] = value;
		break;
	case 72:
		pUserInputAdvanced->TxSlewFallCK[3] = value;
		break;
	case 73:
		pUserInputAdvanced->OdtImpedanceCk[0] = value;
		break;
	case 74:
		pUserInputAdvanced->OdtImpedanceCk[1] = value;
		break;
	case 75:
		pUserInputAdvanced->OdtImpedanceCk[2] = value;
		break;
	case 76:
		pUserInputAdvanced->OdtImpedanceCk[3] = value;
		break;
	case 77:
		pUserInputAdvanced->Lp5xDeassertDramReset = value;
		break;
	case 78:
		pUserInputAdvanced->OdtImpedanceWCK[0] = value;
		break;
	case 79:
		pUserInputAdvanced->OdtImpedanceWCK[1] = value;
		break;
	case 80:
		pUserInputAdvanced->OdtImpedanceWCK[2] = value;
		break;
	case 81:
		pUserInputAdvanced->OdtImpedanceWCK[3] = value;
		break;
	case 82:
		pUserInputAdvanced->EnWck2DqoTracking[0] = value;
		break;
	case 83:
		pUserInputAdvanced->EnWck2DqoTracking[1] = value;
		break;
	case 84:
		pUserInputAdvanced->EnWck2DqoTracking[2] = value;
		break;
	case 85:
		pUserInputAdvanced->EnWck2DqoTracking[3] = value;
		break;
	case 86:
		pUserInputAdvanced->AcInPipeEnOvr = value;
		break;
	case 87:
		pUserInputAdvanced->DtoEnable = value;
		break;
	case 88:
		pUserInputAdvanced->CkDisVal[0] = value;
		break;
	case 89:
		pUserInputAdvanced->CkDisVal[1] = value;
		break;
	case 90:
		pUserInputAdvanced->CkDisVal[2] = value;
		break;
	case 91:
		pUserInputAdvanced->CkDisVal[3] = value;
		break;
	case 92:
		pUserInputAdvanced->DxRdPipeEnOvr = value;
		break;
	case 93:
		pUserInputAdvanced->EnLpRxDqPowerDown = value;
		break;
	case 94:
		pUserInputAdvanced->TxSlewFallDq[0] = value;
		break;
	case 95:
		pUserInputAdvanced->TxSlewFallDq[1] = value;
		break;
	case 96:
		pUserInputAdvanced->TxSlewFallDq[2] = value;
		break;
	case 97:
		pUserInputAdvanced->TxSlewFallDq[3] = value;
		break;
	case 98:
		pUserInputAdvanced->TxImpedanceAc[0] = value;
		break;
	case 99:
		pUserInputAdvanced->TxImpedanceAc[1] = value;
		break;
	case 100:
		pUserInputAdvanced->TxImpedanceAc[2] = value;
		break;
	case 101:
		pUserInputAdvanced->TxImpedanceAc[3] = value;
		break;
	case 102:
		pUserInputAdvanced->CalInterval = value;
		break;
	case 103:
		pUserInputAdvanced->DisableRetraining = value;
		break;
	case 104:
		pUserInputAdvanced->TxImpedanceCk[0] = value;
		break;
	case 105:
		pUserInputAdvanced->TxImpedanceCk[1] = value;
		break;
	case 106:
		pUserInputAdvanced->TxImpedanceCk[2] = value;
		break;
	case 107:
		pUserInputAdvanced->TxImpedanceCk[3] = value;
		break;
	case 108:
		pUserInputAdvanced->DLEPKeyCode = value;
		break;
	case 109:
		pUserInputAdvanced->DxInPipeEn[0] = value;
		break;
	case 110:
		pUserInputAdvanced->DxInPipeEn[1] = value;
		break;
	case 111:
		pUserInputAdvanced->DxInPipeEn[2] = value;
		break;
	case 112:
		pUserInputAdvanced->DxInPipeEn[3] = value;
		break;
	case 113:
		pUserInputAdvanced->EnableSystemEcc = value;
		break;
	case 114:
		pUserInputAdvanced->PHYZCalPowerSaving = value;
		break;
	case 115:
		pUserInputAdvanced->PhyMstrTrainInterval[0] = value;
		break;
	case 116:
		pUserInputAdvanced->PhyMstrTrainInterval[1] = value;
		break;
	case 117:
		pUserInputAdvanced->PhyMstrTrainInterval[2] = value;
		break;
	case 118:
		pUserInputAdvanced->PhyMstrTrainInterval[3] = value;
		break;
	case 119:
		pUserInputAdvanced->DxOutPipeEn[0] = value;
		break;
	case 120:
		pUserInputAdvanced->DxOutPipeEn[1] = value;
		break;
	case 121:
		pUserInputAdvanced->DxOutPipeEn[2] = value;
		break;
	case 122:
		pUserInputAdvanced->DxOutPipeEn[3] = value;
		break;
	case 123:
		pUserInputAdvanced->DisableFspOp = value;
		break;
	case 124:
		pUserInputAdvanced->DfiLpPipeClkDisable = value;
		break;
	case 125:
		pUserInputAdvanced->DisablePclkDca = value;
		break;
	case 126:
		pUserInputAdvanced->RxDqsTrackingThreshold[0] = value;
		break;
	case 127:
		pUserInputAdvanced->RxDqsTrackingThreshold[1] = value;
		break;
	case 128:
		pUserInputAdvanced->RxDqsTrackingThreshold[2] = value;
		break;
	case 129:
		pUserInputAdvanced->RxDqsTrackingThreshold[3] = value;
		break;
	case 130:
		pUserInputAdvanced->TxImpedanceWCK[0] = value;
		break;
	case 131:
		pUserInputAdvanced->TxImpedanceWCK[1] = value;
		break;
	case 132:
		pUserInputAdvanced->TxImpedanceWCK[2] = value;
		break;
	case 133:
		pUserInputAdvanced->TxImpedanceWCK[3] = value;
		break;
	case 134:
		pUserInputAdvanced->OdtImpedanceDqs[0] = value;
		break;
	case 135:
		pUserInputAdvanced->OdtImpedanceDqs[1] = value;
		break;
	case 136:
		pUserInputAdvanced->OdtImpedanceDqs[2] = value;
		break;
	case 137:
		pUserInputAdvanced->OdtImpedanceDqs[3] = value;
		break;
	case 138:
		pUserInputAdvanced->AlertNPipeEn[0] = value;
		break;
	case 139:
		pUserInputAdvanced->AlertNPipeEn[1] = value;
		break;
	case 140:
		pUserInputAdvanced->AlertNPipeEn[2] = value;
		break;
	case 141:
		pUserInputAdvanced->AlertNPipeEn[3] = value;
		break;
	case 142:
		pUserInputAdvanced->SkipFlashCopy[0] = value;
		break;
	case 143:
		pUserInputAdvanced->SkipFlashCopy[1] = value;
		break;
	case 144:
		pUserInputAdvanced->SkipFlashCopy[2] = value;
		break;
	case 145:
		pUserInputAdvanced->SkipFlashCopy[3] = value;
		break;
	case 146:
		pUserInputAdvanced->DxRdPipeEn[0] = value;
		break;
	case 147:
		pUserInputAdvanced->DxRdPipeEn[1] = value;
		break;
	case 148:
		pUserInputAdvanced->DxRdPipeEn[2] = value;
		break;
	case 149:
		pUserInputAdvanced->DxRdPipeEn[3] = value;
		break;
	case 150:
		pUserInputAdvanced->Lp5xFwTinit3WaitTimex1000 = value;
		break;
	case 151:
		pUserInputAdvanced->DisCheckAllUserInputsLegalVal = value;
		break;
	case 152:
		pUserInputAdvanced->SnoopWAEn[0] = value;
		break;
	case 153:
		pUserInputAdvanced->SnoopWAEn[1] = value;
		break;
	case 154:
		pUserInputAdvanced->SnoopWAEn[2] = value;
		break;
	case 155:
		pUserInputAdvanced->SnoopWAEn[3] = value;
		break;
	case 156:
		pUserInputAdvanced->ACDlyScaleGating = value;
		break;
	case 157:
		pUserInputAdvanced->TxSlewRiseDq[0] = value;
		break;
	case 158:
		pUserInputAdvanced->TxSlewRiseDq[1] = value;
		break;
	case 159:
		pUserInputAdvanced->TxSlewRiseDq[2] = value;
		break;
	case 160:
		pUserInputAdvanced->TxSlewRiseDq[3] = value;
		break;
	case 161:
		pUserInputAdvanced->IMEMLoadPerfEn = value;
		break;
	case 162:
		pUserInputAdvanced->AcInPipeEn[0] = value;
		break;
	case 163:
		pUserInputAdvanced->AcInPipeEn[1] = value;
		break;
	case 164:
		pUserInputAdvanced->AcInPipeEn[2] = value;
		break;
	case 165:
		pUserInputAdvanced->AcInPipeEn[3] = value;
		break;
	case 166:
		pUserInputAdvanced->DisCheckImpTxRx[0] = value;
		break;
	case 167:
		pUserInputAdvanced->DisCheckImpTxRx[1] = value;
		break;
	case 168:
		pUserInputAdvanced->DisCheckImpTxRx[2] = value;
		break;
	case 169:
		pUserInputAdvanced->DisCheckImpTxRx[3] = value;
		break;
	case 170:
		pUserInputAdvanced->AcQuarterDataRate = value;
		break;
	case 171:
		pUserInputAdvanced->DisCheckDvfsqDramOdt[0] = value;
		break;
	case 172:
		pUserInputAdvanced->DisCheckDvfsqDramOdt[1] = value;
		break;
	case 173:
		pUserInputAdvanced->DisCheckDvfsqDramOdt[2] = value;
		break;
	case 174:
		pUserInputAdvanced->DisCheckDvfsqDramOdt[3] = value;
		break;
	case 175:
		pUserInputAdvanced->ZcalClkDiv[0] = value;
		break;
	case 176:
		pUserInputAdvanced->ZcalClkDiv[1] = value;
		break;
	case 177:
		pUserInputAdvanced->ZcalClkDiv[2] = value;
		break;
	case 178:
		pUserInputAdvanced->ZcalClkDiv[3] = value;
		break;
	case 179:
		pUserInputAdvanced->OdtImpedanceCa[0] = value;
		break;
	case 180:
		pUserInputAdvanced->OdtImpedanceCa[1] = value;
		break;
	case 181:
		pUserInputAdvanced->OdtImpedanceCa[2] = value;
		break;
	case 182:
		pUserInputAdvanced->OdtImpedanceCa[3] = value;
		break;
	case 183:
		pUserInputAdvanced->RxBiasCurrentControlWck[0] = value;
		break;
	case 184:
		pUserInputAdvanced->RxBiasCurrentControlWck[1] = value;
		break;
	case 185:
		pUserInputAdvanced->RxBiasCurrentControlWck[2] = value;
		break;
	case 186:
		pUserInputAdvanced->RxBiasCurrentControlWck[3] = value;
		break;
	case 187:
		pUserInputAdvanced->PhyMstrMaxReqToAck[0] = value;
		break;
	case 188:
		pUserInputAdvanced->PhyMstrMaxReqToAck[1] = value;
		break;
	case 189:
		pUserInputAdvanced->PhyMstrMaxReqToAck[2] = value;
		break;
	case 190:
		pUserInputAdvanced->PhyMstrMaxReqToAck[3] = value;
		break;
	case 191:
		pUserInputAdvanced->TxSlewRiseCK[0] = value;
		break;
	case 192:
		pUserInputAdvanced->TxSlewRiseCK[1] = value;
		break;
	case 193:
		pUserInputAdvanced->TxSlewRiseCK[2] = value;
		break;
	case 194:
		pUserInputAdvanced->TxSlewRiseCK[3] = value;
		break;
	case 195:
		pUserInputAdvanced->DramByteSwap = value;
		break;
	case 196:
		pUserInputAdvanced->DisZCalOnDataRate = value;
		break;
	case 197:
		pUserInputAdvanced->RxClkTrackEn[0] = value;
		break;
	case 198:
		pUserInputAdvanced->RxClkTrackEn[1] = value;
		break;
	case 199:
		pUserInputAdvanced->RxClkTrackEn[2] = value;
		break;
	case 200:
		pUserInputAdvanced->RxClkTrackEn[3] = value;
		break;
	case 201:
		pUserInputAdvanced->OdtImpedanceDq[0] = value;
		break;
	case 202:
		pUserInputAdvanced->OdtImpedanceDq[1] = value;
		break;
	case 203:
		pUserInputAdvanced->OdtImpedanceDq[2] = value;
		break;
	case 204:
		pUserInputAdvanced->OdtImpedanceDq[3] = value;
		break;
	case 205:
		pUserInputAdvanced->CoreVddScalingMode[0] = value;
		break;
	case 206:
		pUserInputAdvanced->CoreVddScalingMode[1] = value;
		break;
	case 207:
		pUserInputAdvanced->CoreVddScalingMode[2] = value;
		break;
	case 208:
		pUserInputAdvanced->CoreVddScalingMode[3] = value;
		break;
	case 209:
		pUserInputAdvanced->RxDFECtrlDq[0] = value;
		break;
	case 210:
		pUserInputAdvanced->RxDFECtrlDq[1] = value;
		break;
	case 211:
		pUserInputAdvanced->RxDFECtrlDq[2] = value;
		break;
	case 212:
		pUserInputAdvanced->RxDFECtrlDq[3] = value;
		break;
	case 213:
		pUserInputAdvanced->DxInPipeEnOvr = value;
		break;
	case 214:
		pUserInputAdvanced->TxSlewFallCS[0] = value;
		break;
	case 215:
		pUserInputAdvanced->TxSlewFallCS[1] = value;
		break;
	case 216:
		pUserInputAdvanced->TxSlewFallCS[2] = value;
		break;
	case 217:
		pUserInputAdvanced->TxSlewFallCS[3] = value;
		break;
	case 218:
		pUserInputAdvanced->AlertNPipeEnOvr = value;
		break;
	case 219:
		pUserInputAdvanced->SkipPwrDnInRetrain = value;
		break;
	case 220:
		pUserInputAdvanced->TxSlewFallCA[0] = value;
		break;
	case 221:
		pUserInputAdvanced->TxSlewFallCA[1] = value;
		break;
	case 222:
		pUserInputAdvanced->TxSlewFallCA[2] = value;
		break;
	case 223:
		pUserInputAdvanced->TxSlewFallCA[3] = value;
		break;
	case 224:
		pUserInputAdvanced->DqsOscRunTimeSel[0] = value;
		break;
	case 225:
		pUserInputAdvanced->DqsOscRunTimeSel[1] = value;
		break;
	case 226:
		pUserInputAdvanced->DqsOscRunTimeSel[2] = value;
		break;
	case 227:
		pUserInputAdvanced->DqsOscRunTimeSel[3] = value;
		break;
	case 228:
		pUserInputAdvanced->RxBiasCurrentControlRxReplica[0] = value;
		break;
	case 229:
		pUserInputAdvanced->RxBiasCurrentControlRxReplica[1] = value;
		break;
	case 230:
		pUserInputAdvanced->RxBiasCurrentControlRxReplica[2] = value;
		break;
	case 231:
		pUserInputAdvanced->RxBiasCurrentControlRxReplica[3] = value;
		break;
	case 232:
		pUserInputAdvanced->Lp3DramState[0] = value;
		break;
	case 233:
		pUserInputAdvanced->Lp3DramState[1] = value;
		break;
	case 234:
		pUserInputAdvanced->Lp3DramState[2] = value;
		break;
	case 235:
		pUserInputAdvanced->Lp3DramState[3] = value;
		break;
	case 236:
		pUserInputAdvanced->TxSlewRiseCS[0] = value;
		break;
	case 237:
		pUserInputAdvanced->TxSlewRiseCS[1] = value;
		break;
	case 238:
		pUserInputAdvanced->TxSlewRiseCS[2] = value;
		break;
	case 239:
		pUserInputAdvanced->TxSlewRiseCS[3] = value;
		break;
	case 240:
		pUserInputAdvanced->UseSnpsController = value;
		break;
	case 241:
		pUserInputAdvanced->DisRxClkCLcdl[0] = value;
		break;
	case 242:
		pUserInputAdvanced->DisRxClkCLcdl[1] = value;
		break;
	case 243:
		pUserInputAdvanced->DisRxClkCLcdl[2] = value;
		break;
	case 244:
		pUserInputAdvanced->DisRxClkCLcdl[3] = value;
		break;
	case 245:
		pUserInputAdvanced->TxImpedanceDq[0] = value;
		break;
	case 246:
		pUserInputAdvanced->TxImpedanceDq[1] = value;
		break;
	case 247:
		pUserInputAdvanced->TxImpedanceDq[2] = value;
		break;
	case 248:
		pUserInputAdvanced->TxImpedanceDq[3] = value;
		break;
	case 249:
		pUserInputAdvanced->DisablePhyUpdate = value;
		break;
	case 250:
		pUserInputAdvanced->HalfTxCalCode = value;
		break;
	case 251:
		pUserInputAdvanced->DxOutPipeEnOvr = value;
		break;
	case 252:
		pUserInputAdvanced->RetrainMode[0] = value;
		break;
	case 253:
		pUserInputAdvanced->RetrainMode[1] = value;
		break;
	case 254:
		pUserInputAdvanced->RetrainMode[2] = value;
		break;
	case 255:
		pUserInputAdvanced->RetrainMode[3] = value;
		break;
	case 256:
		pUserInputAdvanced->DfiLoopbackEn = value;
		break;
	case 257:
		pUserInputAdvanced->DisablePmuEcc = value;
		break;
	case 258:
		pUserInputAdvanced->TxImpedanceDqs[0] = value;
		break;
	case 259:
		pUserInputAdvanced->TxImpedanceDqs[1] = value;
		break;
	case 260:
		pUserInputAdvanced->TxImpedanceDqs[2] = value;
		break;
	case 261:
		pUserInputAdvanced->TxImpedanceDqs[3] = value;
		break;
	case 262:
		pUserInputAdvanced->TrainSequenceCtrl[0] = value;
		break;
	case 263:
		pUserInputAdvanced->TrainSequenceCtrl[1] = value;
		break;
	case 264:
		pUserInputAdvanced->TrainSequenceCtrl[2] = value;
		break;
	case 265:
		pUserInputAdvanced->TrainSequenceCtrl[3] = value;
		break;
	case 266:
		pUserInputAdvanced->PmuClockDiv[0] = value;
		break;
	case 267:
		pUserInputAdvanced->PmuClockDiv[1] = value;
		break;
	case 268:
		pUserInputAdvanced->PmuClockDiv[2] = value;
		break;
	case 269:
		pUserInputAdvanced->PmuClockDiv[3] = value;
		break;
	case 270:
		pUserInputAdvanced->DqsSampNegRxEnSense[0] = value;
		break;
	case 271:
		pUserInputAdvanced->DqsSampNegRxEnSense[1] = value;
		break;
	case 272:
		pUserInputAdvanced->DqsSampNegRxEnSense[2] = value;
		break;
	case 273:
		pUserInputAdvanced->DqsSampNegRxEnSense[3] = value;
		break;
	case 274:
		pUserInputAdvanced->TxImpedanceCsCke = value;
		break;
	case 275:
		pUserInputBasic->NumPStates = value;
		break;
	case 276:
		pUserInputBasic->NumRank_dfi0 = value;
		break;
	case 277:
		pUserInputBasic->HardMacroVer = value;
		break;
	case 278:
		pUserInputBasic->NumCh = value;
		break;
	case 279:
		pUserInputBasic->DimmType = value;
		break;
	case 280:
		pUserInputBasic->Lp5xMode = value;
		break;
	case 281:
		pUserInputBasic->DramType = value;
		break;
	case 282:
		pUserInputBasic->DfiFreqRatio[0] = value;
		break;
	case 283:
		pUserInputBasic->DfiFreqRatio[1] = value;
		break;
	case 284:
		pUserInputBasic->DfiFreqRatio[2] = value;
		break;
	case 285:
		pUserInputBasic->DfiFreqRatio[3] = value;
		break;
	case 286:
		pUserInputBasic->FirstPState = value;
		break;
	case 287:
		pUserInputBasic->NumActiveDbyteDfi1 = value;
		break;
	case 288:
		pUserInputBasic->NumRank = value;
		break;
	case 289:
		pUserInputBasic->DramDataWidth = value;
		break;
	case 290:
		pUserInputBasic->CfgPStates = value;
		break;
	case 291:
		pUserInputBasic->PclkPtrInitValOvr = value;
		break;
	case 292:
		pUserInputBasic->Frequency[0] = value;
		break;
	case 293:
		pUserInputBasic->Frequency[1] = value;
		break;
	case 294:
		pUserInputBasic->Frequency[2] = value;
		break;
	case 295:
		pUserInputBasic->Frequency[3] = value;
		break;
	case 296:
		pUserInputBasic->PllBypass[0] = value;
		break;
	case 297:
		pUserInputBasic->PllBypass[1] = value;
		break;
	case 298:
		pUserInputBasic->PllBypass[2] = value;
		break;
	case 299:
		pUserInputBasic->PllBypass[3] = value;
		break;
	case 300:
		pUserInputBasic->NumRank_dfi1 = value;
		break;
	case 301:
		pUserInputBasic->NumDbytesPerCh = value;
		break;
	case 302:
		pUserInputBasic->PclkPtrInitVal[0] = value;
		break;
	case 303:
		pUserInputBasic->PclkPtrInitVal[1] = value;
		break;
	case 304:
		pUserInputBasic->PclkPtrInitVal[2] = value;
		break;
	case 305:
		pUserInputBasic->PclkPtrInitVal[3] = value;
		break;
	case 306:
		pUserInputBasic->MaxNumZQ = value;
		break;
	case 307:
		pUserInputBasic->NumActiveDbyteDfi0 = value;
		break;
	case 308:
		pUserInputSim->LcdlRxInsertionDelay = value;
		break;
	case 309:
		pUserInputSim->tWCK2DQO = value;
		break;
	case 310:
		pUserInputSim->tWCK2DQI = value;
		break;
	case 311:
		pUserInputSim->tWCK2CK = value;
		break;
	case 312:
		pUserInputSim->LcdlTxInsertionDelay = value;
		break;
	case 313:
		pUserInputSim->PHY_tDQS2DQ = value;
		break;
	case 314:
		pUserInputSim->RxEnDlyOffset_Reserved = value;
		break;
	case 315:
		pUserInputSim->LcdlNumSteps = value;
		break;
	case 316:
		pUserInputSim->LcdlStepSizex10 = value;
		break;
	default:
		dwc_ddrphy_phyinit_assert(0, " [%s] unknown PhyInit field: '%s' (enum: %d)\n", __func__, dwc_ddrphy_phyinit_setUserInput_enumDecode(field), field);
		result = -1;
		break;
	}
	if (result == 0) {
		dwc_ddrphy_phyinit_cmnt(" [%s] Setting PHYINIT field '%s' (enum: %d) to 0x%x\n", __func__, dwc_ddrphy_phyinit_setUserInput_enumDecode(field), field, value);
	}
	return result;
}

/** @brief API to program PhyInit data structures
 *
 *  This function can be used to program user_input_basic, user_input_advanced,
 *  user_input_sim and runtime_config PhyInit data structures.  PhyInit uses the
 *  information in these data structures to program PHY registers.  For details
 *  information about the fields see the data structure documentation.
 *
 *  Some fields are defined as arrays in the data structure. Example to set
 *  PllBypass for Pstate 3:
 *
 *  @code{.c}
 *  dwc_ddrphy_phyinit_setUserInput("PllBypass[3]", 0x1);
 *  @endcode
 *
 *  \note field strings do not overlap between PhyInit structures.
 *
 *  @param[in]   phyctx  PhyInit context
 *
 *  @param[in]   field   A string representing the field to be programed. bracket
 *  notation can be used to set array fields. example  string: "PllBypass[0]"
 *  set the field UserInputBasic.PllBypass[0].
 *  feilds is an array,
 *
 *  @param[in]   value   Value to be set on the field.
 *
 *  @return 0 on success. -1 when string does not match fields in any of PhyInit
 *  data structures.
 */
int dwc_ddrphy_phyinit_setUserInput(phyinit_config_t *phyctx, char *field, int value)
{
	int fieldEnum;

	if (strcmp(field, "NumAchnActive") == 0) {
		fieldEnum = _NumAchnActive_;
	} else if (strcmp(field, "firstTrainedPState") == 0) {
		fieldEnum = _firstTrainedPState_;
	} else if (strcmp(field, "DataRateMbps[0]") == 0) {
		fieldEnum = _DataRateMbps_0__;
	} else if (strcmp(field, "DataRateMbps[1]") == 0) {
		fieldEnum = _DataRateMbps_1__;
	} else if (strcmp(field, "DataRateMbps[2]") == 0) {
		fieldEnum = _DataRateMbps_2__;
	} else if (strcmp(field, "DataRateMbps[3]") == 0) {
		fieldEnum = _DataRateMbps_3__;
	} else if (strcmp(field, "psExecOrder[0]") == 0) {
		fieldEnum = _psExecOrder_0__;
	} else if (strcmp(field, "psExecOrder[1]") == 0) {
		fieldEnum = _psExecOrder_1__;
	} else if (strcmp(field, "psExecOrder[2]") == 0) {
		fieldEnum = _psExecOrder_2__;
	} else if (strcmp(field, "psExecOrder[3]") == 0) {
		fieldEnum = _psExecOrder_3__;
	} else if (strcmp(field, "NumDbyteActive") == 0) {
		fieldEnum = _NumDbyteActive_;
	} else if (strcmp(field, "enableBits[0]") == 0) {
		fieldEnum = _enableBits_0__;
	} else if (strcmp(field, "enableBits[1]") == 0) {
		fieldEnum = _enableBits_1__;
	} else if (strcmp(field, "enableBits[2]") == 0) {
		fieldEnum = _enableBits_2__;
	} else if (strcmp(field, "NumDxOutPipeEn[0]") == 0) {
		fieldEnum = _NumDxOutPipeEn_0__;
	} else if (strcmp(field, "NumDxOutPipeEn[1]") == 0) {
		fieldEnum = _NumDxOutPipeEn_1__;
	} else if (strcmp(field, "NumDxOutPipeEn[2]") == 0) {
		fieldEnum = _NumDxOutPipeEn_2__;
	} else if (strcmp(field, "NumDxOutPipeEn[3]") == 0) {
		fieldEnum = _NumDxOutPipeEn_3__;
	} else if (strcmp(field, "NumDxInPipeEn[0]") == 0) {
		fieldEnum = _NumDxInPipeEn_0__;
	} else if (strcmp(field, "NumDxInPipeEn[1]") == 0) {
		fieldEnum = _NumDxInPipeEn_1__;
	} else if (strcmp(field, "NumDxInPipeEn[2]") == 0) {
		fieldEnum = _NumDxInPipeEn_2__;
	} else if (strcmp(field, "NumDxInPipeEn[3]") == 0) {
		fieldEnum = _NumDxInPipeEn_3__;
	} else if (strcmp(field, "NumMiscPipeEn[0]") == 0) {
		fieldEnum = _NumMiscPipeEn_0__;
	} else if (strcmp(field, "NumMiscPipeEn[1]") == 0) {
		fieldEnum = _NumMiscPipeEn_1__;
	} else if (strcmp(field, "NumMiscPipeEn[2]") == 0) {
		fieldEnum = _NumMiscPipeEn_2__;
	} else if (strcmp(field, "NumMiscPipeEn[3]") == 0) {
		fieldEnum = _NumMiscPipeEn_3__;
	} else if (strcmp(field, "NumDbyte") == 0) {
		fieldEnum = _NumDbyte_;
	} else if (strcmp(field, "skip_train") == 0) {
		fieldEnum = _skip_train_;
	} else if (strcmp(field, "initCtrl") == 0) {
		fieldEnum = _initCtrl_;
	} else if (strcmp(field, "TG_active[0]") == 0) {
		fieldEnum = _TG_active_0__;
	} else if (strcmp(field, "TG_active[1]") == 0) {
		fieldEnum = _TG_active_1__;
	} else if (strcmp(field, "TG_active[2]") == 0) {
		fieldEnum = _TG_active_2__;
	} else if (strcmp(field, "TG_active[3]") == 0) {
		fieldEnum = _TG_active_3__;
	} else if (strcmp(field, "NumAcInPipeEn[0]") == 0) {
		fieldEnum = _NumAcInPipeEn_0__;
	} else if (strcmp(field, "NumAcInPipeEn[1]") == 0) {
		fieldEnum = _NumAcInPipeEn_1__;
	} else if (strcmp(field, "NumAcInPipeEn[2]") == 0) {
		fieldEnum = _NumAcInPipeEn_2__;
	} else if (strcmp(field, "NumAcInPipeEn[3]") == 0) {
		fieldEnum = _NumAcInPipeEn_3__;
	} else if (strcmp(field, "UcclkFull[0]") == 0) {
		fieldEnum = _UcclkFull_0__;
	} else if (strcmp(field, "UcclkFull[1]") == 0) {
		fieldEnum = _UcclkFull_1__;
	} else if (strcmp(field, "UcclkFull[2]") == 0) {
		fieldEnum = _UcclkFull_2__;
	} else if (strcmp(field, "UcclkFull[3]") == 0) {
		fieldEnum = _UcclkFull_3__;
	} else if (strcmp(field, "DfiFreq[0]") == 0) {
		fieldEnum = _DfiFreq_0__;
	} else if (strcmp(field, "DfiFreq[1]") == 0) {
		fieldEnum = _DfiFreq_1__;
	} else if (strcmp(field, "DfiFreq[2]") == 0) {
		fieldEnum = _DfiFreq_2__;
	} else if (strcmp(field, "DfiFreq[3]") == 0) {
		fieldEnum = _DfiFreq_3__;
	} else if (strcmp(field, "Train2D") == 0) {
		fieldEnum = _Train2D_;
	} else if (strcmp(field, "tck_ps[0]") == 0) {
		fieldEnum = _tck_ps_0__;
	} else if (strcmp(field, "tck_ps[1]") == 0) {
		fieldEnum = _tck_ps_1__;
	} else if (strcmp(field, "tck_ps[2]") == 0) {
		fieldEnum = _tck_ps_2__;
	} else if (strcmp(field, "tck_ps[3]") == 0) {
		fieldEnum = _tck_ps_3__;
	} else if (strcmp(field, "NumAlertNPipeEn[0]") == 0) {
		fieldEnum = _NumAlertNPipeEn_0__;
	} else if (strcmp(field, "NumAlertNPipeEn[1]") == 0) {
		fieldEnum = _NumAlertNPipeEn_1__;
	} else if (strcmp(field, "NumAlertNPipeEn[2]") == 0) {
		fieldEnum = _NumAlertNPipeEn_2__;
	} else if (strcmp(field, "NumAlertNPipeEn[3]") == 0) {
		fieldEnum = _NumAlertNPipeEn_3__;
	} else if (strcmp(field, "pubRev") == 0) {
		fieldEnum = _pubRev_;
	} else if (strcmp(field, "debug") == 0) {
		fieldEnum = _debug_;
	} else if (strcmp(field, "curD") == 0) {
		fieldEnum = _curD_;
	} else if (strcmp(field, "lastTrainedPState") == 0) {
		fieldEnum = _lastTrainedPState_;
	} else if (strcmp(field, "RetEn") == 0) {
		fieldEnum = _RetEn_;
	} else if (strcmp(field, "curPState") == 0) {
		fieldEnum = _curPState_;
	} else if (strcmp(field, "CalImpedanceCurrentAdjustment") == 0) {
		fieldEnum = _CalImpedanceCurrentAdjustment_;
	} else if (strcmp(field, "CalOnce") == 0) {
		fieldEnum = _CalOnce_;
	} else if (strcmp(field, "DMEMLoadPerfEn") == 0) {
		fieldEnum = _DMEMLoadPerfEn_;
	} else if (strcmp(field, "TxSlewRiseCA[0]") == 0) {
		fieldEnum = _TxSlewRiseCA_0__;
	} else if (strcmp(field, "TxSlewRiseCA[1]") == 0) {
		fieldEnum = _TxSlewRiseCA_1__;
	} else if (strcmp(field, "TxSlewRiseCA[2]") == 0) {
		fieldEnum = _TxSlewRiseCA_2__;
	} else if (strcmp(field, "TxSlewRiseCA[3]") == 0) {
		fieldEnum = _TxSlewRiseCA_3__;
	} else if (strcmp(field, "RxGainCtrl") == 0) {
		fieldEnum = _RxGainCtrl_;
	} else if (strcmp(field, "DramStateChangeEn") == 0) {
		fieldEnum = _DramStateChangeEn_;
	} else if (strcmp(field, "TxSlewFallCK[0]") == 0) {
		fieldEnum = _TxSlewFallCK_0__;
	} else if (strcmp(field, "TxSlewFallCK[1]") == 0) {
		fieldEnum = _TxSlewFallCK_1__;
	} else if (strcmp(field, "TxSlewFallCK[2]") == 0) {
		fieldEnum = _TxSlewFallCK_2__;
	} else if (strcmp(field, "TxSlewFallCK[3]") == 0) {
		fieldEnum = _TxSlewFallCK_3__;
	} else if (strcmp(field, "OdtImpedanceCk[0]") == 0) {
		fieldEnum = _OdtImpedanceCk_0__;
	} else if (strcmp(field, "OdtImpedanceCk[1]") == 0) {
		fieldEnum = _OdtImpedanceCk_1__;
	} else if (strcmp(field, "OdtImpedanceCk[2]") == 0) {
		fieldEnum = _OdtImpedanceCk_2__;
	} else if (strcmp(field, "OdtImpedanceCk[3]") == 0) {
		fieldEnum = _OdtImpedanceCk_3__;
	} else if (strcmp(field, "Lp5xDeassertDramReset") == 0) {
		fieldEnum = _Lp5xDeassertDramReset_;
	} else if (strcmp(field, "OdtImpedanceWCK[0]") == 0) {
		fieldEnum = _OdtImpedanceWCK_0__;
	} else if (strcmp(field, "OdtImpedanceWCK[1]") == 0) {
		fieldEnum = _OdtImpedanceWCK_1__;
	} else if (strcmp(field, "OdtImpedanceWCK[2]") == 0) {
		fieldEnum = _OdtImpedanceWCK_2__;
	} else if (strcmp(field, "OdtImpedanceWCK[3]") == 0) {
		fieldEnum = _OdtImpedanceWCK_3__;
	} else if (strcmp(field, "EnWck2DqoTracking[0]") == 0) {
		fieldEnum = _EnWck2DqoTracking_0__;
	} else if (strcmp(field, "EnWck2DqoTracking[1]") == 0) {
		fieldEnum = _EnWck2DqoTracking_1__;
	} else if (strcmp(field, "EnWck2DqoTracking[2]") == 0) {
		fieldEnum = _EnWck2DqoTracking_2__;
	} else if (strcmp(field, "EnWck2DqoTracking[3]") == 0) {
		fieldEnum = _EnWck2DqoTracking_3__;
	} else if (strcmp(field, "AcInPipeEnOvr") == 0) {
		fieldEnum = _AcInPipeEnOvr_;
	} else if (strcmp(field, "DtoEnable") == 0) {
		fieldEnum = _DtoEnable_;
	} else if (strcmp(field, "CkDisVal[0]") == 0) {
		fieldEnum = _CkDisVal_0__;
	} else if (strcmp(field, "CkDisVal[1]") == 0) {
		fieldEnum = _CkDisVal_1__;
	} else if (strcmp(field, "CkDisVal[2]") == 0) {
		fieldEnum = _CkDisVal_2__;
	} else if (strcmp(field, "CkDisVal[3]") == 0) {
		fieldEnum = _CkDisVal_3__;
	} else if (strcmp(field, "DxRdPipeEnOvr") == 0) {
		fieldEnum = _DxRdPipeEnOvr_;
	} else if (strcmp(field, "EnLpRxDqPowerDown") == 0) {
		fieldEnum = _EnLpRxDqPowerDown_;
	} else if (strcmp(field, "TxSlewFallDq[0]") == 0) {
		fieldEnum = _TxSlewFallDq_0__;
	} else if (strcmp(field, "TxSlewFallDq[1]") == 0) {
		fieldEnum = _TxSlewFallDq_1__;
	} else if (strcmp(field, "TxSlewFallDq[2]") == 0) {
		fieldEnum = _TxSlewFallDq_2__;
	} else if (strcmp(field, "TxSlewFallDq[3]") == 0) {
		fieldEnum = _TxSlewFallDq_3__;
	} else if (strcmp(field, "TxImpedanceAc[0]") == 0) {
		fieldEnum = _TxImpedanceAc_0__;
	} else if (strcmp(field, "TxImpedanceAc[1]") == 0) {
		fieldEnum = _TxImpedanceAc_1__;
	} else if (strcmp(field, "TxImpedanceAc[2]") == 0) {
		fieldEnum = _TxImpedanceAc_2__;
	} else if (strcmp(field, "TxImpedanceAc[3]") == 0) {
		fieldEnum = _TxImpedanceAc_3__;
	} else if (strcmp(field, "CalInterval") == 0) {
		fieldEnum = _CalInterval_;
	} else if (strcmp(field, "DisableRetraining") == 0) {
		fieldEnum = _DisableRetraining_;
	} else if (strcmp(field, "TxImpedanceCk[0]") == 0) {
		fieldEnum = _TxImpedanceCk_0__;
	} else if (strcmp(field, "TxImpedanceCk[1]") == 0) {
		fieldEnum = _TxImpedanceCk_1__;
	} else if (strcmp(field, "TxImpedanceCk[2]") == 0) {
		fieldEnum = _TxImpedanceCk_2__;
	} else if (strcmp(field, "TxImpedanceCk[3]") == 0) {
		fieldEnum = _TxImpedanceCk_3__;
	} else if (strcmp(field, "DLEPKeyCode") == 0) {
		fieldEnum = _DLEPKeyCode_;
	} else if (strcmp(field, "DxInPipeEn[0]") == 0) {
		fieldEnum = _DxInPipeEn_0__;
	} else if (strcmp(field, "DxInPipeEn[1]") == 0) {
		fieldEnum = _DxInPipeEn_1__;
	} else if (strcmp(field, "DxInPipeEn[2]") == 0) {
		fieldEnum = _DxInPipeEn_2__;
	} else if (strcmp(field, "DxInPipeEn[3]") == 0) {
		fieldEnum = _DxInPipeEn_3__;
	} else if (strcmp(field, "EnableSystemEcc") == 0) {
		fieldEnum = _EnableSystemEcc_;
	} else if (strcmp(field, "PHYZCalPowerSaving") == 0) {
		fieldEnum = _PHYZCalPowerSaving_;
	} else if (strcmp(field, "PhyMstrTrainInterval[0]") == 0) {
		fieldEnum = _PhyMstrTrainInterval_0__;
	} else if (strcmp(field, "PhyMstrTrainInterval[1]") == 0) {
		fieldEnum = _PhyMstrTrainInterval_1__;
	} else if (strcmp(field, "PhyMstrTrainInterval[2]") == 0) {
		fieldEnum = _PhyMstrTrainInterval_2__;
	} else if (strcmp(field, "PhyMstrTrainInterval[3]") == 0) {
		fieldEnum = _PhyMstrTrainInterval_3__;
	} else if (strcmp(field, "DxOutPipeEn[0]") == 0) {
		fieldEnum = _DxOutPipeEn_0__;
	} else if (strcmp(field, "DxOutPipeEn[1]") == 0) {
		fieldEnum = _DxOutPipeEn_1__;
	} else if (strcmp(field, "DxOutPipeEn[2]") == 0) {
		fieldEnum = _DxOutPipeEn_2__;
	} else if (strcmp(field, "DxOutPipeEn[3]") == 0) {
		fieldEnum = _DxOutPipeEn_3__;
	} else if (strcmp(field, "DisableFspOp") == 0) {
		fieldEnum = _DisableFspOp_;
	} else if (strcmp(field, "DfiLpPipeClkDisable") == 0) {
		fieldEnum = _DfiLpPipeClkDisable_;
	} else if (strcmp(field, "DisablePclkDca") == 0) {
		fieldEnum = _DisablePclkDca_;
	} else if (strcmp(field, "RxDqsTrackingThreshold[0]") == 0) {
		fieldEnum = _RxDqsTrackingThreshold_0__;
	} else if (strcmp(field, "RxDqsTrackingThreshold[1]") == 0) {
		fieldEnum = _RxDqsTrackingThreshold_1__;
	} else if (strcmp(field, "RxDqsTrackingThreshold[2]") == 0) {
		fieldEnum = _RxDqsTrackingThreshold_2__;
	} else if (strcmp(field, "RxDqsTrackingThreshold[3]") == 0) {
		fieldEnum = _RxDqsTrackingThreshold_3__;
	} else if (strcmp(field, "TxImpedanceWCK[0]") == 0) {
		fieldEnum = _TxImpedanceWCK_0__;
	} else if (strcmp(field, "TxImpedanceWCK[1]") == 0) {
		fieldEnum = _TxImpedanceWCK_1__;
	} else if (strcmp(field, "TxImpedanceWCK[2]") == 0) {
		fieldEnum = _TxImpedanceWCK_2__;
	} else if (strcmp(field, "TxImpedanceWCK[3]") == 0) {
		fieldEnum = _TxImpedanceWCK_3__;
	} else if (strcmp(field, "OdtImpedanceDqs[0]") == 0) {
		fieldEnum = _OdtImpedanceDqs_0__;
	} else if (strcmp(field, "OdtImpedanceDqs[1]") == 0) {
		fieldEnum = _OdtImpedanceDqs_1__;
	} else if (strcmp(field, "OdtImpedanceDqs[2]") == 0) {
		fieldEnum = _OdtImpedanceDqs_2__;
	} else if (strcmp(field, "OdtImpedanceDqs[3]") == 0) {
		fieldEnum = _OdtImpedanceDqs_3__;
	} else if (strcmp(field, "AlertNPipeEn[0]") == 0) {
		fieldEnum = _AlertNPipeEn_0__;
	} else if (strcmp(field, "AlertNPipeEn[1]") == 0) {
		fieldEnum = _AlertNPipeEn_1__;
	} else if (strcmp(field, "AlertNPipeEn[2]") == 0) {
		fieldEnum = _AlertNPipeEn_2__;
	} else if (strcmp(field, "AlertNPipeEn[3]") == 0) {
		fieldEnum = _AlertNPipeEn_3__;
	} else if (strcmp(field, "SkipFlashCopy[0]") == 0) {
		fieldEnum = _SkipFlashCopy_0__;
	} else if (strcmp(field, "SkipFlashCopy[1]") == 0) {
		fieldEnum = _SkipFlashCopy_1__;
	} else if (strcmp(field, "SkipFlashCopy[2]") == 0) {
		fieldEnum = _SkipFlashCopy_2__;
	} else if (strcmp(field, "SkipFlashCopy[3]") == 0) {
		fieldEnum = _SkipFlashCopy_3__;
	} else if (strcmp(field, "DxRdPipeEn[0]") == 0) {
		fieldEnum = _DxRdPipeEn_0__;
	} else if (strcmp(field, "DxRdPipeEn[1]") == 0) {
		fieldEnum = _DxRdPipeEn_1__;
	} else if (strcmp(field, "DxRdPipeEn[2]") == 0) {
		fieldEnum = _DxRdPipeEn_2__;
	} else if (strcmp(field, "DxRdPipeEn[3]") == 0) {
		fieldEnum = _DxRdPipeEn_3__;
	} else if (strcmp(field, "Lp5xFwTinit3WaitTimex1000") == 0) {
		fieldEnum = _Lp5xFwTinit3WaitTimex1000_;
	} else if (strcmp(field, "DisCheckAllUserInputsLegalVal") == 0) {
		fieldEnum = _DisCheckAllUserInputsLegalVal_;
	} else if (strcmp(field, "SnoopWAEn[0]") == 0) {
		fieldEnum = _SnoopWAEn_0__;
	} else if (strcmp(field, "SnoopWAEn[1]") == 0) {
		fieldEnum = _SnoopWAEn_1__;
	} else if (strcmp(field, "SnoopWAEn[2]") == 0) {
		fieldEnum = _SnoopWAEn_2__;
	} else if (strcmp(field, "SnoopWAEn[3]") == 0) {
		fieldEnum = _SnoopWAEn_3__;
	} else if (strcmp(field, "ACDlyScaleGating") == 0) {
		fieldEnum = _ACDlyScaleGating_;
	} else if (strcmp(field, "TxSlewRiseDq[0]") == 0) {
		fieldEnum = _TxSlewRiseDq_0__;
	} else if (strcmp(field, "TxSlewRiseDq[1]") == 0) {
		fieldEnum = _TxSlewRiseDq_1__;
	} else if (strcmp(field, "TxSlewRiseDq[2]") == 0) {
		fieldEnum = _TxSlewRiseDq_2__;
	} else if (strcmp(field, "TxSlewRiseDq[3]") == 0) {
		fieldEnum = _TxSlewRiseDq_3__;
	} else if (strcmp(field, "IMEMLoadPerfEn") == 0) {
		fieldEnum = _IMEMLoadPerfEn_;
	} else if (strcmp(field, "AcInPipeEn[0]") == 0) {
		fieldEnum = _AcInPipeEn_0__;
	} else if (strcmp(field, "AcInPipeEn[1]") == 0) {
		fieldEnum = _AcInPipeEn_1__;
	} else if (strcmp(field, "AcInPipeEn[2]") == 0) {
		fieldEnum = _AcInPipeEn_2__;
	} else if (strcmp(field, "AcInPipeEn[3]") == 0) {
		fieldEnum = _AcInPipeEn_3__;
	} else if (strcmp(field, "DisCheckImpTxRx[0]") == 0) {
		fieldEnum = _DisCheckImpTxRx_0__;
	} else if (strcmp(field, "DisCheckImpTxRx[1]") == 0) {
		fieldEnum = _DisCheckImpTxRx_1__;
	} else if (strcmp(field, "DisCheckImpTxRx[2]") == 0) {
		fieldEnum = _DisCheckImpTxRx_2__;
	} else if (strcmp(field, "DisCheckImpTxRx[3]") == 0) {
		fieldEnum = _DisCheckImpTxRx_3__;
	} else if (strcmp(field, "AcQuarterDataRate") == 0) {
		fieldEnum = _AcQuarterDataRate_;
	} else if (strcmp(field, "DisCheckDvfsqDramOdt[0]") == 0) {
		fieldEnum = _DisCheckDvfsqDramOdt_0__;
	} else if (strcmp(field, "DisCheckDvfsqDramOdt[1]") == 0) {
		fieldEnum = _DisCheckDvfsqDramOdt_1__;
	} else if (strcmp(field, "DisCheckDvfsqDramOdt[2]") == 0) {
		fieldEnum = _DisCheckDvfsqDramOdt_2__;
	} else if (strcmp(field, "DisCheckDvfsqDramOdt[3]") == 0) {
		fieldEnum = _DisCheckDvfsqDramOdt_3__;
	} else if (strcmp(field, "ZcalClkDiv[0]") == 0) {
		fieldEnum = _ZcalClkDiv_0__;
	} else if (strcmp(field, "ZcalClkDiv[1]") == 0) {
		fieldEnum = _ZcalClkDiv_1__;
	} else if (strcmp(field, "ZcalClkDiv[2]") == 0) {
		fieldEnum = _ZcalClkDiv_2__;
	} else if (strcmp(field, "ZcalClkDiv[3]") == 0) {
		fieldEnum = _ZcalClkDiv_3__;
	} else if (strcmp(field, "OdtImpedanceCa[0]") == 0) {
		fieldEnum = _OdtImpedanceCa_0__;
	} else if (strcmp(field, "OdtImpedanceCa[1]") == 0) {
		fieldEnum = _OdtImpedanceCa_1__;
	} else if (strcmp(field, "OdtImpedanceCa[2]") == 0) {
		fieldEnum = _OdtImpedanceCa_2__;
	} else if (strcmp(field, "OdtImpedanceCa[3]") == 0) {
		fieldEnum = _OdtImpedanceCa_3__;
	} else if (strcmp(field, "RxBiasCurrentControlWck[0]") == 0) {
		fieldEnum = _RxBiasCurrentControlWck_0__;
	} else if (strcmp(field, "RxBiasCurrentControlWck[1]") == 0) {
		fieldEnum = _RxBiasCurrentControlWck_1__;
	} else if (strcmp(field, "RxBiasCurrentControlWck[2]") == 0) {
		fieldEnum = _RxBiasCurrentControlWck_2__;
	} else if (strcmp(field, "RxBiasCurrentControlWck[3]") == 0) {
		fieldEnum = _RxBiasCurrentControlWck_3__;
	} else if (strcmp(field, "PhyMstrMaxReqToAck[0]") == 0) {
		fieldEnum = _PhyMstrMaxReqToAck_0__;
	} else if (strcmp(field, "PhyMstrMaxReqToAck[1]") == 0) {
		fieldEnum = _PhyMstrMaxReqToAck_1__;
	} else if (strcmp(field, "PhyMstrMaxReqToAck[2]") == 0) {
		fieldEnum = _PhyMstrMaxReqToAck_2__;
	} else if (strcmp(field, "PhyMstrMaxReqToAck[3]") == 0) {
		fieldEnum = _PhyMstrMaxReqToAck_3__;
	} else if (strcmp(field, "TxSlewRiseCK[0]") == 0) {
		fieldEnum = _TxSlewRiseCK_0__;
	} else if (strcmp(field, "TxSlewRiseCK[1]") == 0) {
		fieldEnum = _TxSlewRiseCK_1__;
	} else if (strcmp(field, "TxSlewRiseCK[2]") == 0) {
		fieldEnum = _TxSlewRiseCK_2__;
	} else if (strcmp(field, "TxSlewRiseCK[3]") == 0) {
		fieldEnum = _TxSlewRiseCK_3__;
	} else if (strcmp(field, "DramByteSwap") == 0) {
		fieldEnum = _DramByteSwap_;
	} else if (strcmp(field, "DisZCalOnDataRate") == 0) {
		fieldEnum = _DisZCalOnDataRate_;
	} else if (strcmp(field, "RxClkTrackEn[0]") == 0) {
		fieldEnum = _RxClkTrackEn_0__;
	} else if (strcmp(field, "RxClkTrackEn[1]") == 0) {
		fieldEnum = _RxClkTrackEn_1__;
	} else if (strcmp(field, "RxClkTrackEn[2]") == 0) {
		fieldEnum = _RxClkTrackEn_2__;
	} else if (strcmp(field, "RxClkTrackEn[3]") == 0) {
		fieldEnum = _RxClkTrackEn_3__;
	} else if (strcmp(field, "OdtImpedanceDq[0]") == 0) {
		fieldEnum = _OdtImpedanceDq_0__;
	} else if (strcmp(field, "OdtImpedanceDq[1]") == 0) {
		fieldEnum = _OdtImpedanceDq_1__;
	} else if (strcmp(field, "OdtImpedanceDq[2]") == 0) {
		fieldEnum = _OdtImpedanceDq_2__;
	} else if (strcmp(field, "OdtImpedanceDq[3]") == 0) {
		fieldEnum = _OdtImpedanceDq_3__;
	} else if (strcmp(field, "CoreVddScalingMode[0]") == 0) {
		fieldEnum = _CoreVddScalingMode_0__;
	} else if (strcmp(field, "CoreVddScalingMode[1]") == 0) {
		fieldEnum = _CoreVddScalingMode_1__;
	} else if (strcmp(field, "CoreVddScalingMode[2]") == 0) {
		fieldEnum = _CoreVddScalingMode_2__;
	} else if (strcmp(field, "CoreVddScalingMode[3]") == 0) {
		fieldEnum = _CoreVddScalingMode_3__;
	} else if (strcmp(field, "RxDFECtrlDq[0]") == 0) {
		fieldEnum = _RxDFECtrlDq_0__;
	} else if (strcmp(field, "RxDFECtrlDq[1]") == 0) {
		fieldEnum = _RxDFECtrlDq_1__;
	} else if (strcmp(field, "RxDFECtrlDq[2]") == 0) {
		fieldEnum = _RxDFECtrlDq_2__;
	} else if (strcmp(field, "RxDFECtrlDq[3]") == 0) {
		fieldEnum = _RxDFECtrlDq_3__;
	} else if (strcmp(field, "DxInPipeEnOvr") == 0) {
		fieldEnum = _DxInPipeEnOvr_;
	} else if (strcmp(field, "TxSlewFallCS[0]") == 0) {
		fieldEnum = _TxSlewFallCS_0__;
	} else if (strcmp(field, "TxSlewFallCS[1]") == 0) {
		fieldEnum = _TxSlewFallCS_1__;
	} else if (strcmp(field, "TxSlewFallCS[2]") == 0) {
		fieldEnum = _TxSlewFallCS_2__;
	} else if (strcmp(field, "TxSlewFallCS[3]") == 0) {
		fieldEnum = _TxSlewFallCS_3__;
	} else if (strcmp(field, "AlertNPipeEnOvr") == 0) {
		fieldEnum = _AlertNPipeEnOvr_;
	} else if (strcmp(field, "SkipPwrDnInRetrain") == 0) {
		fieldEnum = _SkipPwrDnInRetrain_;
	} else if (strcmp(field, "TxSlewFallCA[0]") == 0) {
		fieldEnum = _TxSlewFallCA_0__;
	} else if (strcmp(field, "TxSlewFallCA[1]") == 0) {
		fieldEnum = _TxSlewFallCA_1__;
	} else if (strcmp(field, "TxSlewFallCA[2]") == 0) {
		fieldEnum = _TxSlewFallCA_2__;
	} else if (strcmp(field, "TxSlewFallCA[3]") == 0) {
		fieldEnum = _TxSlewFallCA_3__;
	} else if (strcmp(field, "DqsOscRunTimeSel[0]") == 0) {
		fieldEnum = _DqsOscRunTimeSel_0__;
	} else if (strcmp(field, "DqsOscRunTimeSel[1]") == 0) {
		fieldEnum = _DqsOscRunTimeSel_1__;
	} else if (strcmp(field, "DqsOscRunTimeSel[2]") == 0) {
		fieldEnum = _DqsOscRunTimeSel_2__;
	} else if (strcmp(field, "DqsOscRunTimeSel[3]") == 0) {
		fieldEnum = _DqsOscRunTimeSel_3__;
	} else if (strcmp(field, "RxBiasCurrentControlRxReplica[0]") == 0) {
		fieldEnum = _RxBiasCurrentControlRxReplica_0__;
	} else if (strcmp(field, "RxBiasCurrentControlRxReplica[1]") == 0) {
		fieldEnum = _RxBiasCurrentControlRxReplica_1__;
	} else if (strcmp(field, "RxBiasCurrentControlRxReplica[2]") == 0) {
		fieldEnum = _RxBiasCurrentControlRxReplica_2__;
	} else if (strcmp(field, "RxBiasCurrentControlRxReplica[3]") == 0) {
		fieldEnum = _RxBiasCurrentControlRxReplica_3__;
	} else if (strcmp(field, "Lp3DramState[0]") == 0) {
		fieldEnum = _Lp3DramState_0__;
	} else if (strcmp(field, "Lp3DramState[1]") == 0) {
		fieldEnum = _Lp3DramState_1__;
	} else if (strcmp(field, "Lp3DramState[2]") == 0) {
		fieldEnum = _Lp3DramState_2__;
	} else if (strcmp(field, "Lp3DramState[3]") == 0) {
		fieldEnum = _Lp3DramState_3__;
	} else if (strcmp(field, "TxSlewRiseCS[0]") == 0) {
		fieldEnum = _TxSlewRiseCS_0__;
	} else if (strcmp(field, "TxSlewRiseCS[1]") == 0) {
		fieldEnum = _TxSlewRiseCS_1__;
	} else if (strcmp(field, "TxSlewRiseCS[2]") == 0) {
		fieldEnum = _TxSlewRiseCS_2__;
	} else if (strcmp(field, "TxSlewRiseCS[3]") == 0) {
		fieldEnum = _TxSlewRiseCS_3__;
	} else if (strcmp(field, "UseSnpsController") == 0) {
		fieldEnum = _UseSnpsController_;
	} else if (strcmp(field, "DisRxClkCLcdl[0]") == 0) {
		fieldEnum = _DisRxClkCLcdl_0__;
	} else if (strcmp(field, "DisRxClkCLcdl[1]") == 0) {
		fieldEnum = _DisRxClkCLcdl_1__;
	} else if (strcmp(field, "DisRxClkCLcdl[2]") == 0) {
		fieldEnum = _DisRxClkCLcdl_2__;
	} else if (strcmp(field, "DisRxClkCLcdl[3]") == 0) {
		fieldEnum = _DisRxClkCLcdl_3__;
	} else if (strcmp(field, "TxImpedanceDq[0]") == 0) {
		fieldEnum = _TxImpedanceDq_0__;
	} else if (strcmp(field, "TxImpedanceDq[1]") == 0) {
		fieldEnum = _TxImpedanceDq_1__;
	} else if (strcmp(field, "TxImpedanceDq[2]") == 0) {
		fieldEnum = _TxImpedanceDq_2__;
	} else if (strcmp(field, "TxImpedanceDq[3]") == 0) {
		fieldEnum = _TxImpedanceDq_3__;
	} else if (strcmp(field, "DisablePhyUpdate") == 0) {
		fieldEnum = _DisablePhyUpdate_;
	} else if (strcmp(field, "HalfTxCalCode") == 0) {
		fieldEnum = _HalfTxCalCode_;
	} else if (strcmp(field, "DxOutPipeEnOvr") == 0) {
		fieldEnum = _DxOutPipeEnOvr_;
	} else if (strcmp(field, "RetrainMode[0]") == 0) {
		fieldEnum = _RetrainMode_0__;
	} else if (strcmp(field, "RetrainMode[1]") == 0) {
		fieldEnum = _RetrainMode_1__;
	} else if (strcmp(field, "RetrainMode[2]") == 0) {
		fieldEnum = _RetrainMode_2__;
	} else if (strcmp(field, "RetrainMode[3]") == 0) {
		fieldEnum = _RetrainMode_3__;
	} else if (strcmp(field, "DfiLoopbackEn") == 0) {
		fieldEnum = _DfiLoopbackEn_;
	} else if (strcmp(field, "DisablePmuEcc") == 0) {
		fieldEnum = _DisablePmuEcc_;
	} else if (strcmp(field, "TxImpedanceDqs[0]") == 0) {
		fieldEnum = _TxImpedanceDqs_0__;
	} else if (strcmp(field, "TxImpedanceDqs[1]") == 0) {
		fieldEnum = _TxImpedanceDqs_1__;
	} else if (strcmp(field, "TxImpedanceDqs[2]") == 0) {
		fieldEnum = _TxImpedanceDqs_2__;
	} else if (strcmp(field, "TxImpedanceDqs[3]") == 0) {
		fieldEnum = _TxImpedanceDqs_3__;
	} else if (strcmp(field, "TrainSequenceCtrl[0]") == 0) {
		fieldEnum = _TrainSequenceCtrl_0__;
	} else if (strcmp(field, "TrainSequenceCtrl[1]") == 0) {
		fieldEnum = _TrainSequenceCtrl_1__;
	} else if (strcmp(field, "TrainSequenceCtrl[2]") == 0) {
		fieldEnum = _TrainSequenceCtrl_2__;
	} else if (strcmp(field, "TrainSequenceCtrl[3]") == 0) {
		fieldEnum = _TrainSequenceCtrl_3__;
	} else if (strcmp(field, "PmuClockDiv[0]") == 0) {
		fieldEnum = _PmuClockDiv_0__;
	} else if (strcmp(field, "PmuClockDiv[1]") == 0) {
		fieldEnum = _PmuClockDiv_1__;
	} else if (strcmp(field, "PmuClockDiv[2]") == 0) {
		fieldEnum = _PmuClockDiv_2__;
	} else if (strcmp(field, "PmuClockDiv[3]") == 0) {
		fieldEnum = _PmuClockDiv_3__;
	} else if (strcmp(field, "DqsSampNegRxEnSense[0]") == 0) {
		fieldEnum = _DqsSampNegRxEnSense_0__;
	} else if (strcmp(field, "DqsSampNegRxEnSense[1]") == 0) {
		fieldEnum = _DqsSampNegRxEnSense_1__;
	} else if (strcmp(field, "DqsSampNegRxEnSense[2]") == 0) {
		fieldEnum = _DqsSampNegRxEnSense_2__;
	} else if (strcmp(field, "DqsSampNegRxEnSense[3]") == 0) {
		fieldEnum = _DqsSampNegRxEnSense_3__;
	} else if (strcmp(field, "TxImpedanceCsCke") == 0) {
		fieldEnum = _TxImpedanceCsCke_;
	} else if (strcmp(field, "NumPStates") == 0) {
		fieldEnum = _NumPStates_;
	} else if (strcmp(field, "NumRank_dfi0") == 0) {
		fieldEnum = _NumRank_dfi0_;
	} else if (strcmp(field, "HardMacroVer") == 0) {
		fieldEnum = _HardMacroVer_;
	} else if (strcmp(field, "NumCh") == 0) {
		fieldEnum = _NumCh_;
	} else if (strcmp(field, "DimmType") == 0) {
		fieldEnum = _DimmType_;
	} else if (strcmp(field, "Lp5xMode") == 0) {
		fieldEnum = _Lp5xMode_;
	} else if (strcmp(field, "DramType") == 0) {
		fieldEnum = _DramType_;
	} else if (strcmp(field, "DfiFreqRatio[0]") == 0) {
		fieldEnum = _DfiFreqRatio_0__;
	} else if (strcmp(field, "DfiFreqRatio[1]") == 0) {
		fieldEnum = _DfiFreqRatio_1__;
	} else if (strcmp(field, "DfiFreqRatio[2]") == 0) {
		fieldEnum = _DfiFreqRatio_2__;
	} else if (strcmp(field, "DfiFreqRatio[3]") == 0) {
		fieldEnum = _DfiFreqRatio_3__;
	} else if (strcmp(field, "FirstPState") == 0) {
		fieldEnum = _FirstPState_;
	} else if (strcmp(field, "NumActiveDbyteDfi1") == 0) {
		fieldEnum = _NumActiveDbyteDfi1_;
	} else if (strcmp(field, "NumRank") == 0) {
		fieldEnum = _NumRank_;
	} else if (strcmp(field, "DramDataWidth") == 0) {
		fieldEnum = _DramDataWidth_;
	} else if (strcmp(field, "CfgPStates") == 0) {
		fieldEnum = _CfgPStates_;
	} else if (strcmp(field, "PclkPtrInitValOvr") == 0) {
		fieldEnum = _PclkPtrInitValOvr_;
	} else if (strcmp(field, "Frequency[0]") == 0) {
		fieldEnum = _Frequency_0__;
	} else if (strcmp(field, "Frequency[1]") == 0) {
		fieldEnum = _Frequency_1__;
	} else if (strcmp(field, "Frequency[2]") == 0) {
		fieldEnum = _Frequency_2__;
	} else if (strcmp(field, "Frequency[3]") == 0) {
		fieldEnum = _Frequency_3__;
	} else if (strcmp(field, "PllBypass[0]") == 0) {
		fieldEnum = _PllBypass_0__;
	} else if (strcmp(field, "PllBypass[1]") == 0) {
		fieldEnum = _PllBypass_1__;
	} else if (strcmp(field, "PllBypass[2]") == 0) {
		fieldEnum = _PllBypass_2__;
	} else if (strcmp(field, "PllBypass[3]") == 0) {
		fieldEnum = _PllBypass_3__;
	} else if (strcmp(field, "NumRank_dfi1") == 0) {
		fieldEnum = _NumRank_dfi1_;
	} else if (strcmp(field, "NumDbytesPerCh") == 0) {
		fieldEnum = _NumDbytesPerCh_;
	} else if (strcmp(field, "PclkPtrInitVal[0]") == 0) {
		fieldEnum = _PclkPtrInitVal_0__;
	} else if (strcmp(field, "PclkPtrInitVal[1]") == 0) {
		fieldEnum = _PclkPtrInitVal_1__;
	} else if (strcmp(field, "PclkPtrInitVal[2]") == 0) {
		fieldEnum = _PclkPtrInitVal_2__;
	} else if (strcmp(field, "PclkPtrInitVal[3]") == 0) {
		fieldEnum = _PclkPtrInitVal_3__;
	} else if (strcmp(field, "MaxNumZQ") == 0) {
		fieldEnum = _MaxNumZQ_;
	} else if (strcmp(field, "NumActiveDbyteDfi0") == 0) {
		fieldEnum = _NumActiveDbyteDfi0_;
	} else if (strcmp(field, "LcdlRxInsertionDelay") == 0) {
		fieldEnum = _LcdlRxInsertionDelay_;
	} else if (strcmp(field, "tWCK2DQO") == 0) {
		fieldEnum = _tWCK2DQO_;
	} else if (strcmp(field, "tWCK2DQI") == 0) {
		fieldEnum = _tWCK2DQI_;
	} else if (strcmp(field, "tWCK2CK") == 0) {
		fieldEnum = _tWCK2CK_;
	} else if (strcmp(field, "LcdlTxInsertionDelay") == 0) {
		fieldEnum = _LcdlTxInsertionDelay_;
	} else if (strcmp(field, "PHY_tDQS2DQ") == 0) {
		fieldEnum = _PHY_tDQS2DQ_;
	} else if (strcmp(field, "RxEnDlyOffset_Reserved") == 0) {
		fieldEnum = _RxEnDlyOffset_Reserved_;
	} else if (strcmp(field, "LcdlNumSteps") == 0) {
		fieldEnum = _LcdlNumSteps_;
	} else if (strcmp(field, "LcdlStepSizex10") == 0) {
		fieldEnum = _LcdlStepSizex10_;
	} else {
		fieldEnum = -1;
		dwc_ddrphy_phyinit_assert(0, " [%s] unknown PhyInit field name '%s'\n", __func__, field);
	}
	return dwc_ddrphy_phyinit_setUserInput_enum(phyctx, fieldEnum, value);
}

/** @} */
