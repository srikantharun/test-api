/** \file
 * \brief sets messageBlock variables
 * \addtogroup SrcFunc
 *  @{
 */
#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** @brief API to program the Message Block
 *
 *  This function can be used to program training firmware 1D/2D message block fields
 *  for a given PState.  as an example, to program MsgMsic to 0x4 for Pstate 3,
 *  for 1D Training :
 *  @code{.c}
 *  dwc_ddrphy_phyinit_setMB(3, "MsgMisc", 0x4, 0);
 *  @endcode
 *
 * refer to the messageBlock data structure for definition of fields
 * applicable to each protocol.
 *
 * @param[in]   phyctx  PhyInit context
 *
 * @param[in]   ps	  integer between 0-3. Specifies the PState for which the
 * messageBlock field should be set.
 *
 * @param[in]   field   A string representing the messageBlock field to be
 * programed.
 *
 * @param[in]   value   filed value
 *
 * @return 0 on success. On error  returns the following values based on
 * error:
 * - -1 : message block field specified by the input \c field string is not
 * found in the message block data structure.
 * - -2 : when DramType does not support 2D training but a 2D training field is
 * programmed.
 * - -3 : Train2D inputs is neither 1 or 0.
 */
int dwc_ddrphy_phyinit_setMb(phyinit_config_t *phyctx, int ps, char *field, int value)
{
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	int Train2D = pRuntimeConfig->Train2D;

	PMU_SMB_LPDDR5X_1D_t *mb_LPDDR5X_1D = phyctx->mb_LPDDR5X_1D;
	PMU_SMB_LPDDR5X_1D_t *shdw_LPDDR5X_1D = phyctx->shdw_LPDDR5X_1D;

	if (Train2D == 0) {
		if (strcmp(field, "Reserved00") == 0) {
			mb_LPDDR5X_1D[ps].Reserved00 = value;
			shdw_LPDDR5X_1D[ps].Reserved00 = 1;
		} else if (strcmp(field, "MsgMisc") == 0) {
			mb_LPDDR5X_1D[ps].MsgMisc = value;
			shdw_LPDDR5X_1D[ps].MsgMisc = 1;
		} else if (strcmp(field, "Pstate") == 0) {
			mb_LPDDR5X_1D[ps].Pstate = value;
			shdw_LPDDR5X_1D[ps].Pstate = 1;
		} else if (strcmp(field, "PllBypassEn") == 0) {
			mb_LPDDR5X_1D[ps].PllBypassEn = value;
			shdw_LPDDR5X_1D[ps].PllBypassEn = 1;
		} else if (strcmp(field, "DRAMFreq") == 0) {
			mb_LPDDR5X_1D[ps].DRAMFreq = value;
			shdw_LPDDR5X_1D[ps].DRAMFreq = 1;
		} else if (strcmp(field, "DfiFreqRatio") == 0) {
			mb_LPDDR5X_1D[ps].DfiFreqRatio = value;
			shdw_LPDDR5X_1D[ps].DfiFreqRatio = 1;
		} else if (strcmp(field, "DcaOpts") == 0) {
			mb_LPDDR5X_1D[ps].DcaOpts = value;
			shdw_LPDDR5X_1D[ps].DcaOpts = 1;
		} else if (strcmp(field, "Train2DMisc") == 0) {
			mb_LPDDR5X_1D[ps].Train2DMisc = value;
			shdw_LPDDR5X_1D[ps].Train2DMisc = 1;
		} else if (strcmp(field, "UseAltRxPath") == 0) {
			mb_LPDDR5X_1D[ps].UseAltRxPath = value;
			shdw_LPDDR5X_1D[ps].UseAltRxPath = 1;
		} else if (strcmp(field, "Misc") == 0) {
			mb_LPDDR5X_1D[ps].Misc = value;
			shdw_LPDDR5X_1D[ps].Misc = 1;
		} else if (strcmp(field, "SIFriendlyDlyOffset") == 0) {
			mb_LPDDR5X_1D[ps].SIFriendlyDlyOffset = value;
			shdw_LPDDR5X_1D[ps].SIFriendlyDlyOffset = 1;
		} else if (strcmp(field, "SequenceCtrl") == 0) {
			mb_LPDDR5X_1D[ps].SequenceCtrl = value;
			shdw_LPDDR5X_1D[ps].SequenceCtrl = 1;
		} else if (strcmp(field, "HdtCtrl") == 0) {
			mb_LPDDR5X_1D[ps].HdtCtrl = value;
			shdw_LPDDR5X_1D[ps].HdtCtrl = 1;
		} else if (strcmp(field, "Reserved13") == 0) {
			mb_LPDDR5X_1D[ps].Reserved13 = value;
			shdw_LPDDR5X_1D[ps].Reserved13 = 1;
		} else if (strcmp(field, "DFIMRLMargin") == 0) {
			mb_LPDDR5X_1D[ps].DFIMRLMargin = value;
			shdw_LPDDR5X_1D[ps].DFIMRLMargin = 1;
		} else if (strcmp(field, "TX2D_Delay_Weight") == 0) {
			mb_LPDDR5X_1D[ps].TX2D_Delay_Weight = value;
			shdw_LPDDR5X_1D[ps].TX2D_Delay_Weight = 1;
		} else if (strcmp(field, "TX2D_Voltage_Weight") == 0) {
			mb_LPDDR5X_1D[ps].TX2D_Voltage_Weight = value;
			shdw_LPDDR5X_1D[ps].TX2D_Voltage_Weight = 1;
		} else if (strcmp(field, "Quickboot") == 0) {
			mb_LPDDR5X_1D[ps].Quickboot = value;
			shdw_LPDDR5X_1D[ps].Quickboot = 1;
		} else if (strcmp(field, "CaTrainAltUpdate") == 0) {
			mb_LPDDR5X_1D[ps].CaTrainAltUpdate = value;
			shdw_LPDDR5X_1D[ps].CaTrainAltUpdate = 1;
		} else if (strcmp(field, "CATrainOpt") == 0) {
			mb_LPDDR5X_1D[ps].CATrainOpt = value;
			shdw_LPDDR5X_1D[ps].CATrainOpt = 1;
		} else if (strcmp(field, "X8Mode") == 0) {
			mb_LPDDR5X_1D[ps].X8Mode = value;
			shdw_LPDDR5X_1D[ps].X8Mode = 1;
		} else if (strcmp(field, "RX2D_TrainOpt") == 0) {
			mb_LPDDR5X_1D[ps].RX2D_TrainOpt = value;
			shdw_LPDDR5X_1D[ps].RX2D_TrainOpt = 1;
		} else if (strcmp(field, "TX2D_TrainOpt") == 0) {
			mb_LPDDR5X_1D[ps].TX2D_TrainOpt = value;
			shdw_LPDDR5X_1D[ps].TX2D_TrainOpt = 1;
		} else if (strcmp(field, "RxDFEOpt") == 0) {
			mb_LPDDR5X_1D[ps].RxDFEOpt = value;
			shdw_LPDDR5X_1D[ps].RxDFEOpt = 1;
		} else if (strcmp(field, "RX2D_Delay_Weight") == 0) {
			mb_LPDDR5X_1D[ps].RX2D_Delay_Weight = value;
			shdw_LPDDR5X_1D[ps].RX2D_Delay_Weight = 1;
		} else if (strcmp(field, "RX2D_Voltage_Weight") == 0) {
			mb_LPDDR5X_1D[ps].RX2D_Voltage_Weight = value;
			shdw_LPDDR5X_1D[ps].RX2D_Voltage_Weight = 1;
		} else if (strcmp(field, "PhyConfigOverride") == 0) {
			mb_LPDDR5X_1D[ps].PhyConfigOverride = value;
			shdw_LPDDR5X_1D[ps].PhyConfigOverride = 1;
		} else if (strcmp(field, "EnabledDQsChA") == 0) {
			mb_LPDDR5X_1D[ps].EnabledDQsChA = value;
			shdw_LPDDR5X_1D[ps].EnabledDQsChA = 1;
		} else if (strcmp(field, "CsPresentChA") == 0) {
			mb_LPDDR5X_1D[ps].CsPresentChA = value;
			shdw_LPDDR5X_1D[ps].CsPresentChA = 1;
		} else if (strcmp(field, "CATerminatingRankChA") == 0) {
			mb_LPDDR5X_1D[ps].CATerminatingRankChA = value;
			shdw_LPDDR5X_1D[ps].CATerminatingRankChA = 1;
		} else if (strcmp(field, "EnabledDQsChB") == 0) {
			mb_LPDDR5X_1D[ps].EnabledDQsChB = value;
			shdw_LPDDR5X_1D[ps].EnabledDQsChB = 1;
		} else if (strcmp(field, "CsPresentChB") == 0) {
			mb_LPDDR5X_1D[ps].CsPresentChB = value;
			shdw_LPDDR5X_1D[ps].CsPresentChB = 1;
		} else if (strcmp(field, "CATerminatingRankChB") == 0) {
			mb_LPDDR5X_1D[ps].CATerminatingRankChB = value;
			shdw_LPDDR5X_1D[ps].CATerminatingRankChB = 1;
		} else if (strcmp(field, "MR1_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR1_A0 = value;
			shdw_LPDDR5X_1D[ps].MR1_A0 = 1;
		} else if (strcmp(field, "MR1_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR1_A1 = value;
			shdw_LPDDR5X_1D[ps].MR1_A1 = 1;
		} else if (strcmp(field, "MR1_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR1_B0 = value;
			shdw_LPDDR5X_1D[ps].MR1_B0 = 1;
		} else if (strcmp(field, "MR1_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR1_B1 = value;
			shdw_LPDDR5X_1D[ps].MR1_B1 = 1;
		} else if (strcmp(field, "MR2_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR2_A0 = value;
			shdw_LPDDR5X_1D[ps].MR2_A0 = 1;
		} else if (strcmp(field, "MR2_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR2_A1 = value;
			shdw_LPDDR5X_1D[ps].MR2_A1 = 1;
		} else if (strcmp(field, "MR2_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR2_B0 = value;
			shdw_LPDDR5X_1D[ps].MR2_B0 = 1;
		} else if (strcmp(field, "MR2_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR2_B1 = value;
			shdw_LPDDR5X_1D[ps].MR2_B1 = 1;
		} else if (strcmp(field, "MR3_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR3_A0 = value;
			shdw_LPDDR5X_1D[ps].MR3_A0 = 1;
		} else if (strcmp(field, "MR3_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR3_A1 = value;
			shdw_LPDDR5X_1D[ps].MR3_A1 = 1;
		} else if (strcmp(field, "MR3_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR3_B0 = value;
			shdw_LPDDR5X_1D[ps].MR3_B0 = 1;
		} else if (strcmp(field, "MR3_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR3_B1 = value;
			shdw_LPDDR5X_1D[ps].MR3_B1 = 1;
		} else if (strcmp(field, "MR10_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR10_A0 = value;
			shdw_LPDDR5X_1D[ps].MR10_A0 = 1;
		} else if (strcmp(field, "MR10_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR10_A1 = value;
			shdw_LPDDR5X_1D[ps].MR10_A1 = 1;
		} else if (strcmp(field, "MR10_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR10_B0 = value;
			shdw_LPDDR5X_1D[ps].MR10_B0 = 1;
		} else if (strcmp(field, "MR10_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR10_B1 = value;
			shdw_LPDDR5X_1D[ps].MR10_B1 = 1;
		} else if (strcmp(field, "MR11_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR11_A0 = value;
			shdw_LPDDR5X_1D[ps].MR11_A0 = 1;
		} else if (strcmp(field, "MR11_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR11_A1 = value;
			shdw_LPDDR5X_1D[ps].MR11_A1 = 1;
		} else if (strcmp(field, "MR11_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR11_B0 = value;
			shdw_LPDDR5X_1D[ps].MR11_B0 = 1;
		} else if (strcmp(field, "MR11_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR11_B1 = value;
			shdw_LPDDR5X_1D[ps].MR11_B1 = 1;
		} else if (strcmp(field, "MR12_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR12_A0 = value;
			shdw_LPDDR5X_1D[ps].MR12_A0 = 1;
		} else if (strcmp(field, "MR12_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR12_A1 = value;
			shdw_LPDDR5X_1D[ps].MR12_A1 = 1;
		} else if (strcmp(field, "MR12_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR12_B0 = value;
			shdw_LPDDR5X_1D[ps].MR12_B0 = 1;
		} else if (strcmp(field, "MR12_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR12_B1 = value;
			shdw_LPDDR5X_1D[ps].MR12_B1 = 1;
		} else if (strcmp(field, "MR13_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR13_A0 = value;
			shdw_LPDDR5X_1D[ps].MR13_A0 = 1;
		} else if (strcmp(field, "MR13_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR13_A1 = value;
			shdw_LPDDR5X_1D[ps].MR13_A1 = 1;
		} else if (strcmp(field, "MR13_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR13_B0 = value;
			shdw_LPDDR5X_1D[ps].MR13_B0 = 1;
		} else if (strcmp(field, "MR13_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR13_B1 = value;
			shdw_LPDDR5X_1D[ps].MR13_B1 = 1;
		} else if (strcmp(field, "MR14_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR14_A0 = value;
			shdw_LPDDR5X_1D[ps].MR14_A0 = 1;
		} else if (strcmp(field, "MR14_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR14_A1 = value;
			shdw_LPDDR5X_1D[ps].MR14_A1 = 1;
		} else if (strcmp(field, "MR14_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR14_B0 = value;
			shdw_LPDDR5X_1D[ps].MR14_B0 = 1;
		} else if (strcmp(field, "MR14_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR14_B1 = value;
			shdw_LPDDR5X_1D[ps].MR14_B1 = 1;
		} else if (strcmp(field, "MR15_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR15_A0 = value;
			shdw_LPDDR5X_1D[ps].MR15_A0 = 1;
		} else if (strcmp(field, "MR15_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR15_A1 = value;
			shdw_LPDDR5X_1D[ps].MR15_A1 = 1;
		} else if (strcmp(field, "MR15_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR15_B0 = value;
			shdw_LPDDR5X_1D[ps].MR15_B0 = 1;
		} else if (strcmp(field, "MR15_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR15_B1 = value;
			shdw_LPDDR5X_1D[ps].MR15_B1 = 1;
		} else if (strcmp(field, "MR16_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR16_A0 = value;
			shdw_LPDDR5X_1D[ps].MR16_A0 = 1;
		} else if (strcmp(field, "MR16_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR16_A1 = value;
			shdw_LPDDR5X_1D[ps].MR16_A1 = 1;
		} else if (strcmp(field, "MR16_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR16_B0 = value;
			shdw_LPDDR5X_1D[ps].MR16_B0 = 1;
		} else if (strcmp(field, "MR16_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR16_B1 = value;
			shdw_LPDDR5X_1D[ps].MR16_B1 = 1;
		} else if (strcmp(field, "MR17_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR17_A0 = value;
			shdw_LPDDR5X_1D[ps].MR17_A0 = 1;
		} else if (strcmp(field, "MR17_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR17_A1 = value;
			shdw_LPDDR5X_1D[ps].MR17_A1 = 1;
		} else if (strcmp(field, "MR17_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR17_B0 = value;
			shdw_LPDDR5X_1D[ps].MR17_B0 = 1;
		} else if (strcmp(field, "MR17_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR17_B1 = value;
			shdw_LPDDR5X_1D[ps].MR17_B1 = 1;
		} else if (strcmp(field, "MR18_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR18_A0 = value;
			shdw_LPDDR5X_1D[ps].MR18_A0 = 1;
		} else if (strcmp(field, "MR18_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR18_A1 = value;
			shdw_LPDDR5X_1D[ps].MR18_A1 = 1;
		} else if (strcmp(field, "MR18_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR18_B0 = value;
			shdw_LPDDR5X_1D[ps].MR18_B0 = 1;
		} else if (strcmp(field, "MR18_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR18_B1 = value;
			shdw_LPDDR5X_1D[ps].MR18_B1 = 1;
		} else if (strcmp(field, "MR19_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR19_A0 = value;
			shdw_LPDDR5X_1D[ps].MR19_A0 = 1;
		} else if (strcmp(field, "MR19_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR19_A1 = value;
			shdw_LPDDR5X_1D[ps].MR19_A1 = 1;
		} else if (strcmp(field, "MR19_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR19_B0 = value;
			shdw_LPDDR5X_1D[ps].MR19_B0 = 1;
		} else if (strcmp(field, "MR19_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR19_B1 = value;
			shdw_LPDDR5X_1D[ps].MR19_B1 = 1;
		} else if (strcmp(field, "MR20_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR20_A0 = value;
			shdw_LPDDR5X_1D[ps].MR20_A0 = 1;
		} else if (strcmp(field, "MR20_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR20_A1 = value;
			shdw_LPDDR5X_1D[ps].MR20_A1 = 1;
		} else if (strcmp(field, "MR20_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR20_B0 = value;
			shdw_LPDDR5X_1D[ps].MR20_B0 = 1;
		} else if (strcmp(field, "MR20_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR20_B1 = value;
			shdw_LPDDR5X_1D[ps].MR20_B1 = 1;
		} else if (strcmp(field, "MR21_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR21_A0 = value;
			shdw_LPDDR5X_1D[ps].MR21_A0 = 1;
		} else if (strcmp(field, "MR21_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR21_A1 = value;
			shdw_LPDDR5X_1D[ps].MR21_A1 = 1;
		} else if (strcmp(field, "MR21_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR21_B0 = value;
			shdw_LPDDR5X_1D[ps].MR21_B0 = 1;
		} else if (strcmp(field, "MR21_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR21_B1 = value;
			shdw_LPDDR5X_1D[ps].MR21_B1 = 1;
		} else if (strcmp(field, "MR22_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR22_A0 = value;
			shdw_LPDDR5X_1D[ps].MR22_A0 = 1;
		} else if (strcmp(field, "MR22_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR22_A1 = value;
			shdw_LPDDR5X_1D[ps].MR22_A1 = 1;
		} else if (strcmp(field, "MR22_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR22_B0 = value;
			shdw_LPDDR5X_1D[ps].MR22_B0 = 1;
		} else if (strcmp(field, "MR22_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR22_B1 = value;
			shdw_LPDDR5X_1D[ps].MR22_B1 = 1;
		} else if (strcmp(field, "MR24_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR24_A0 = value;
			shdw_LPDDR5X_1D[ps].MR24_A0 = 1;
		} else if (strcmp(field, "MR24_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR24_A1 = value;
			shdw_LPDDR5X_1D[ps].MR24_A1 = 1;
		} else if (strcmp(field, "MR24_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR24_B0 = value;
			shdw_LPDDR5X_1D[ps].MR24_B0 = 1;
		} else if (strcmp(field, "MR24_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR24_B1 = value;
			shdw_LPDDR5X_1D[ps].MR24_B1 = 1;
		} else if (strcmp(field, "MR25_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR25_A0 = value;
			shdw_LPDDR5X_1D[ps].MR25_A0 = 1;
		} else if (strcmp(field, "MR25_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR25_A1 = value;
			shdw_LPDDR5X_1D[ps].MR25_A1 = 1;
		} else if (strcmp(field, "MR25_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR25_B0 = value;
			shdw_LPDDR5X_1D[ps].MR25_B0 = 1;
		} else if (strcmp(field, "MR25_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR25_B1 = value;
			shdw_LPDDR5X_1D[ps].MR25_B1 = 1;
		} else if (strcmp(field, "MR26_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR26_A0 = value;
			shdw_LPDDR5X_1D[ps].MR26_A0 = 1;
		} else if (strcmp(field, "MR26_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR26_A1 = value;
			shdw_LPDDR5X_1D[ps].MR26_A1 = 1;
		} else if (strcmp(field, "MR26_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR26_B0 = value;
			shdw_LPDDR5X_1D[ps].MR26_B0 = 1;
		} else if (strcmp(field, "MR26_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR26_B1 = value;
			shdw_LPDDR5X_1D[ps].MR26_B1 = 1;
		} else if (strcmp(field, "MR27_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR27_A0 = value;
			shdw_LPDDR5X_1D[ps].MR27_A0 = 1;
		} else if (strcmp(field, "MR27_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR27_A1 = value;
			shdw_LPDDR5X_1D[ps].MR27_A1 = 1;
		} else if (strcmp(field, "MR27_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR27_B0 = value;
			shdw_LPDDR5X_1D[ps].MR27_B0 = 1;
		} else if (strcmp(field, "MR27_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR27_B1 = value;
			shdw_LPDDR5X_1D[ps].MR27_B1 = 1;
		} else if (strcmp(field, "MR28_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR28_A0 = value;
			shdw_LPDDR5X_1D[ps].MR28_A0 = 1;
		} else if (strcmp(field, "MR28_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR28_A1 = value;
			shdw_LPDDR5X_1D[ps].MR28_A1 = 1;
		} else if (strcmp(field, "MR28_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR28_B0 = value;
			shdw_LPDDR5X_1D[ps].MR28_B0 = 1;
		} else if (strcmp(field, "MR28_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR28_B1 = value;
			shdw_LPDDR5X_1D[ps].MR28_B1 = 1;
		} else if (strcmp(field, "MR30_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR30_A0 = value;
			shdw_LPDDR5X_1D[ps].MR30_A0 = 1;
		} else if (strcmp(field, "MR30_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR30_A1 = value;
			shdw_LPDDR5X_1D[ps].MR30_A1 = 1;
		} else if (strcmp(field, "MR30_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR30_B0 = value;
			shdw_LPDDR5X_1D[ps].MR30_B0 = 1;
		} else if (strcmp(field, "MR30_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR30_B1 = value;
			shdw_LPDDR5X_1D[ps].MR30_B1 = 1;
		} else if (strcmp(field, "MR31_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR31_A0 = value;
			shdw_LPDDR5X_1D[ps].MR31_A0 = 1;
		} else if (strcmp(field, "MR31_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR31_A1 = value;
			shdw_LPDDR5X_1D[ps].MR31_A1 = 1;
		} else if (strcmp(field, "MR31_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR31_B0 = value;
			shdw_LPDDR5X_1D[ps].MR31_B0 = 1;
		} else if (strcmp(field, "MR31_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR31_B1 = value;
			shdw_LPDDR5X_1D[ps].MR31_B1 = 1;
		} else if (strcmp(field, "MR32_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR32_A0 = value;
			shdw_LPDDR5X_1D[ps].MR32_A0 = 1;
		} else if (strcmp(field, "MR32_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR32_A1 = value;
			shdw_LPDDR5X_1D[ps].MR32_A1 = 1;
		} else if (strcmp(field, "MR32_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR32_B0 = value;
			shdw_LPDDR5X_1D[ps].MR32_B0 = 1;
		} else if (strcmp(field, "MR32_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR32_B1 = value;
			shdw_LPDDR5X_1D[ps].MR32_B1 = 1;
		} else if (strcmp(field, "MR33_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR33_A0 = value;
			shdw_LPDDR5X_1D[ps].MR33_A0 = 1;
		} else if (strcmp(field, "MR33_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR33_A1 = value;
			shdw_LPDDR5X_1D[ps].MR33_A1 = 1;
		} else if (strcmp(field, "MR33_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR33_B0 = value;
			shdw_LPDDR5X_1D[ps].MR33_B0 = 1;
		} else if (strcmp(field, "MR33_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR33_B1 = value;
			shdw_LPDDR5X_1D[ps].MR33_B1 = 1;
		} else if (strcmp(field, "MR34_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR34_A0 = value;
			shdw_LPDDR5X_1D[ps].MR34_A0 = 1;
		} else if (strcmp(field, "MR34_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR34_A1 = value;
			shdw_LPDDR5X_1D[ps].MR34_A1 = 1;
		} else if (strcmp(field, "MR34_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR34_B0 = value;
			shdw_LPDDR5X_1D[ps].MR34_B0 = 1;
		} else if (strcmp(field, "MR34_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR34_B1 = value;
			shdw_LPDDR5X_1D[ps].MR34_B1 = 1;
		} else if (strcmp(field, "MR37_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR37_A0 = value;
			shdw_LPDDR5X_1D[ps].MR37_A0 = 1;
		} else if (strcmp(field, "MR37_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR37_A1 = value;
			shdw_LPDDR5X_1D[ps].MR37_A1 = 1;
		} else if (strcmp(field, "MR37_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR37_B0 = value;
			shdw_LPDDR5X_1D[ps].MR37_B0 = 1;
		} else if (strcmp(field, "MR37_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR37_B1 = value;
			shdw_LPDDR5X_1D[ps].MR37_B1 = 1;
		} else if (strcmp(field, "MR40_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR40_A0 = value;
			shdw_LPDDR5X_1D[ps].MR40_A0 = 1;
		} else if (strcmp(field, "MR40_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR40_A1 = value;
			shdw_LPDDR5X_1D[ps].MR40_A1 = 1;
		} else if (strcmp(field, "MR40_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR40_B0 = value;
			shdw_LPDDR5X_1D[ps].MR40_B0 = 1;
		} else if (strcmp(field, "MR40_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR40_B1 = value;
			shdw_LPDDR5X_1D[ps].MR40_B1 = 1;
		} else if (strcmp(field, "MR41_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR41_A0 = value;
			shdw_LPDDR5X_1D[ps].MR41_A0 = 1;
		} else if (strcmp(field, "MR41_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR41_A1 = value;
			shdw_LPDDR5X_1D[ps].MR41_A1 = 1;
		} else if (strcmp(field, "MR41_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR41_B0 = value;
			shdw_LPDDR5X_1D[ps].MR41_B0 = 1;
		} else if (strcmp(field, "MR41_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR41_B1 = value;
			shdw_LPDDR5X_1D[ps].MR41_B1 = 1;
		} else if (strcmp(field, "MR57_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR57_A0 = value;
			shdw_LPDDR5X_1D[ps].MR57_A0 = 1;
		} else if (strcmp(field, "MR57_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR57_A1 = value;
			shdw_LPDDR5X_1D[ps].MR57_A1 = 1;
		} else if (strcmp(field, "MR57_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR57_B0 = value;
			shdw_LPDDR5X_1D[ps].MR57_B0 = 1;
		} else if (strcmp(field, "MR57_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR57_B1 = value;
			shdw_LPDDR5X_1D[ps].MR57_B1 = 1;
		} else if (strcmp(field, "MR58_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR58_A0 = value;
			shdw_LPDDR5X_1D[ps].MR58_A0 = 1;
		} else if (strcmp(field, "MR58_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR58_A1 = value;
			shdw_LPDDR5X_1D[ps].MR58_A1 = 1;
		} else if (strcmp(field, "MR58_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR58_B0 = value;
			shdw_LPDDR5X_1D[ps].MR58_B0 = 1;
		} else if (strcmp(field, "MR58_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR58_B1 = value;
			shdw_LPDDR5X_1D[ps].MR58_B1 = 1;
		} else if (strcmp(field, "MR69_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR69_A0 = value;
			shdw_LPDDR5X_1D[ps].MR69_A0 = 1;
		} else if (strcmp(field, "MR69_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR69_A1 = value;
			shdw_LPDDR5X_1D[ps].MR69_A1 = 1;
		} else if (strcmp(field, "MR69_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR69_B0 = value;
			shdw_LPDDR5X_1D[ps].MR69_B0 = 1;
		} else if (strcmp(field, "MR69_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR69_B1 = value;
			shdw_LPDDR5X_1D[ps].MR69_B1 = 1;
		} else if (strcmp(field, "MR70_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR70_A0 = value;
			shdw_LPDDR5X_1D[ps].MR70_A0 = 1;
		} else if (strcmp(field, "MR70_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR70_A1 = value;
			shdw_LPDDR5X_1D[ps].MR70_A1 = 1;
		} else if (strcmp(field, "MR70_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR70_B0 = value;
			shdw_LPDDR5X_1D[ps].MR70_B0 = 1;
		} else if (strcmp(field, "MR70_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR70_B1 = value;
			shdw_LPDDR5X_1D[ps].MR70_B1 = 1;
		} else if (strcmp(field, "MR71_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR71_A0 = value;
			shdw_LPDDR5X_1D[ps].MR71_A0 = 1;
		} else if (strcmp(field, "MR71_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR71_A1 = value;
			shdw_LPDDR5X_1D[ps].MR71_A1 = 1;
		} else if (strcmp(field, "MR71_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR71_B0 = value;
			shdw_LPDDR5X_1D[ps].MR71_B0 = 1;
		} else if (strcmp(field, "MR71_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR71_B1 = value;
			shdw_LPDDR5X_1D[ps].MR71_B1 = 1;
		} else if (strcmp(field, "MR72_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR72_A0 = value;
			shdw_LPDDR5X_1D[ps].MR72_A0 = 1;
		} else if (strcmp(field, "MR72_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR72_A1 = value;
			shdw_LPDDR5X_1D[ps].MR72_A1 = 1;
		} else if (strcmp(field, "MR72_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR72_B0 = value;
			shdw_LPDDR5X_1D[ps].MR72_B0 = 1;
		} else if (strcmp(field, "MR72_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR72_B1 = value;
			shdw_LPDDR5X_1D[ps].MR72_B1 = 1;
		} else if (strcmp(field, "MR73_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR73_A0 = value;
			shdw_LPDDR5X_1D[ps].MR73_A0 = 1;
		} else if (strcmp(field, "MR73_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR73_A1 = value;
			shdw_LPDDR5X_1D[ps].MR73_A1 = 1;
		} else if (strcmp(field, "MR73_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR73_B0 = value;
			shdw_LPDDR5X_1D[ps].MR73_B0 = 1;
		} else if (strcmp(field, "MR73_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR73_B1 = value;
			shdw_LPDDR5X_1D[ps].MR73_B1 = 1;
		} else if (strcmp(field, "MR74_A0") == 0) {
			mb_LPDDR5X_1D[ps].MR74_A0 = value;
			shdw_LPDDR5X_1D[ps].MR74_A0 = 1;
		} else if (strcmp(field, "MR74_A1") == 0) {
			mb_LPDDR5X_1D[ps].MR74_A1 = value;
			shdw_LPDDR5X_1D[ps].MR74_A1 = 1;
		} else if (strcmp(field, "MR74_B0") == 0) {
			mb_LPDDR5X_1D[ps].MR74_B0 = value;
			shdw_LPDDR5X_1D[ps].MR74_B0 = 1;
		} else if (strcmp(field, "MR74_B1") == 0) {
			mb_LPDDR5X_1D[ps].MR74_B1 = value;
			shdw_LPDDR5X_1D[ps].MR74_B1 = 1;
		} else if (strcmp(field, "Disable2D") == 0) {
			mb_LPDDR5X_1D[ps].Disable2D = value;
			shdw_LPDDR5X_1D[ps].Disable2D = 1;
		} else if (strcmp(field, "PPT2OffsetMargin") == 0) {
			mb_LPDDR5X_1D[ps].PPT2OffsetMargin = value;
			shdw_LPDDR5X_1D[ps].PPT2OffsetMargin = 1;
		} else if (strcmp(field, "forceRxReplica") == 0) {
			mb_LPDDR5X_1D[ps].forceRxReplica = value;
			shdw_LPDDR5X_1D[ps].forceRxReplica = 1;
		} else if (strcmp(field, "HardwareScans") == 0) {
			mb_LPDDR5X_1D[ps].HardwareScans = value;
			shdw_LPDDR5X_1D[ps].HardwareScans = 1;
		} else if (strcmp(field, "TxDFETrainOpt") == 0) {
			mb_LPDDR5X_1D[ps].TxDFETrainOpt = value;
			shdw_LPDDR5X_1D[ps].TxDFETrainOpt = 1;
		} else if (strcmp(field, "SDOpt") == 0) {
			mb_LPDDR5X_1D[ps].SDOpt = value;
			shdw_LPDDR5X_1D[ps].SDOpt = 1;
		} else if (strcmp(field, "RdWrPatternA") == 0) {
			mb_LPDDR5X_1D[ps].RdWrPatternA = value;
			shdw_LPDDR5X_1D[ps].RdWrPatternA = 1;
		} else if (strcmp(field, "RdWrPatternB") == 0) {
			mb_LPDDR5X_1D[ps].RdWrPatternB = value;
			shdw_LPDDR5X_1D[ps].RdWrPatternB = 1;
		} else if (strcmp(field, "RdWrInvert") == 0) {
			mb_LPDDR5X_1D[ps].RdWrInvert = value;
			shdw_LPDDR5X_1D[ps].RdWrInvert = 1;
		} else if (strcmp(field, "LdffMode") == 0) {
			mb_LPDDR5X_1D[ps].LdffMode = value;
			shdw_LPDDR5X_1D[ps].LdffMode = 1;
		} else if (strcmp(field, "FCDfi0AcsmStart") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi0AcsmStart = value;
			shdw_LPDDR5X_1D[ps].FCDfi0AcsmStart = 1;
		} else if (strcmp(field, "FCDfi1AcsmStart") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi1AcsmStart = value;
			shdw_LPDDR5X_1D[ps].FCDfi1AcsmStart = 1;
		} else if (strcmp(field, "FCDfi0AcsmStartPSY") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPSY = value;
			shdw_LPDDR5X_1D[ps].FCDfi0AcsmStartPSY = 1;
		} else if (strcmp(field, "FCDfi1AcsmStartPSY") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPSY = value;
			shdw_LPDDR5X_1D[ps].FCDfi1AcsmStartPSY = 1;
		} else if (strcmp(field, "FCDMAStartMR") == 0) {
			mb_LPDDR5X_1D[ps].FCDMAStartMR = value;
			shdw_LPDDR5X_1D[ps].FCDMAStartMR = 1;
		} else if (strcmp(field, "FCDMAStartCsr") == 0) {
			mb_LPDDR5X_1D[ps].FCDMAStartCsr = value;
			shdw_LPDDR5X_1D[ps].FCDMAStartCsr = 1;
		} else if (strcmp(field, "EnCustomSettings") == 0) {
			mb_LPDDR5X_1D[ps].EnCustomSettings = value;
			shdw_LPDDR5X_1D[ps].EnCustomSettings = 1;
		} else if (strcmp(field, "LSTxSlewCK") == 0) {
			mb_LPDDR5X_1D[ps].LSTxSlewCK = value;
			shdw_LPDDR5X_1D[ps].LSTxSlewCK = 1;
		} else if (strcmp(field, "LSTxSlewCS") == 0) {
			mb_LPDDR5X_1D[ps].LSTxSlewCS = value;
			shdw_LPDDR5X_1D[ps].LSTxSlewCS = 1;
		} else if (strcmp(field, "LSTxSlewCA") == 0) {
			mb_LPDDR5X_1D[ps].LSTxSlewCA = value;
			shdw_LPDDR5X_1D[ps].LSTxSlewCA = 1;
		} else if (strcmp(field, "LSTxImpedanceCK") == 0) {
			mb_LPDDR5X_1D[ps].LSTxImpedanceCK = value;
			shdw_LPDDR5X_1D[ps].LSTxImpedanceCK = 1;
		} else if (strcmp(field, "LSTxImpedanceCS") == 0) {
			mb_LPDDR5X_1D[ps].LSTxImpedanceCS = value;
			shdw_LPDDR5X_1D[ps].LSTxImpedanceCS = 1;
		} else if (strcmp(field, "LSTxImpedanceCA") == 0) {
			mb_LPDDR5X_1D[ps].LSTxImpedanceCA = value;
			shdw_LPDDR5X_1D[ps].LSTxImpedanceCA = 1;
		} else if (strcmp(field, "VrefFilterAboveVal") == 0) {
			mb_LPDDR5X_1D[ps].VrefFilterAboveVal = value;
			shdw_LPDDR5X_1D[ps].VrefFilterAboveVal = 1;
		} else if (strcmp(field, "VrefFilterBelowVal") == 0) {
			mb_LPDDR5X_1D[ps].VrefFilterBelowVal = value;
			shdw_LPDDR5X_1D[ps].VrefFilterBelowVal = 1;
		} else if (strcmp(field, "EMOpt") == 0) {
			mb_LPDDR5X_1D[ps].EMOpt = value;
			shdw_LPDDR5X_1D[ps].EMOpt = 1;
		} else if (strcmp(field, "VrefInc") == 0) {
			mb_LPDDR5X_1D[ps].VrefInc = value;
			shdw_LPDDR5X_1D[ps].VrefInc = 1;
		} else if (strcmp(field, "UpperLowerByte") == 0) {
			mb_LPDDR5X_1D[ps].UpperLowerByte = value;
			shdw_LPDDR5X_1D[ps].UpperLowerByte = 1;
		} else if (strcmp(field, "ALT_RL") == 0) {
			mb_LPDDR5X_1D[ps].ALT_RL = value;
			shdw_LPDDR5X_1D[ps].ALT_RL = 1;
		} else if (strcmp(field, "MAIN_RL") == 0) {
			mb_LPDDR5X_1D[ps].MAIN_RL = value;
			shdw_LPDDR5X_1D[ps].MAIN_RL = 1;
		} else if (strcmp(field, "CSBACKOFF") == 0) {
			mb_LPDDR5X_1D[ps].CSBACKOFF = value;
			shdw_LPDDR5X_1D[ps].CSBACKOFF = 1;
		} else if (strcmp(field, "WrLvlTrainOpt") == 0) {
			mb_LPDDR5X_1D[ps].WrLvlTrainOpt = value;
			shdw_LPDDR5X_1D[ps].WrLvlTrainOpt = 1;
		} else if (strcmp(field, "MRLCalcAdj") == 0) {
			mb_LPDDR5X_1D[ps].MRLCalcAdj = value;
			shdw_LPDDR5X_1D[ps].MRLCalcAdj = 1;
		} else if (strcmp(field, "LP5XMode") == 0) {
			mb_LPDDR5X_1D[ps].LP5XMode = value;
			shdw_LPDDR5X_1D[ps].LP5XMode = 1;
		} else if (strcmp(field, "RxVrefStartPat") == 0) {
			mb_LPDDR5X_1D[ps].RxVrefStartPat = value;
			shdw_LPDDR5X_1D[ps].RxVrefStartPat = 1;
		} else if (strcmp(field, "RxVrefStartPrbs") == 0) {
			mb_LPDDR5X_1D[ps].RxVrefStartPrbs = value;
			shdw_LPDDR5X_1D[ps].RxVrefStartPrbs = 1;
		} else if (strcmp(field, "RxVrefEndPat") == 0) {
			mb_LPDDR5X_1D[ps].RxVrefEndPat = value;
			shdw_LPDDR5X_1D[ps].RxVrefEndPat = 1;
		} else if (strcmp(field, "RxVrefEndPrbs") == 0) {
			mb_LPDDR5X_1D[ps].RxVrefEndPrbs = value;
			shdw_LPDDR5X_1D[ps].RxVrefEndPrbs = 1;
		} else if (strcmp(field, "TxVrefStart") == 0) {
			mb_LPDDR5X_1D[ps].TxVrefStart = value;
			shdw_LPDDR5X_1D[ps].TxVrefStart = 1;
		} else if (strcmp(field, "TxVrefEnd") == 0) {
			mb_LPDDR5X_1D[ps].TxVrefEnd = value;
			shdw_LPDDR5X_1D[ps].TxVrefEnd = 1;
		} else if (strcmp(field, "RxVrefStepPat") == 0) {
			mb_LPDDR5X_1D[ps].RxVrefStepPat = value;
			shdw_LPDDR5X_1D[ps].RxVrefStepPat = 1;
		} else if (strcmp(field, "RxVrefStepPrbs") == 0) {
			mb_LPDDR5X_1D[ps].RxVrefStepPrbs = value;
			shdw_LPDDR5X_1D[ps].RxVrefStepPrbs = 1;
		} else if (strcmp(field, "TxVrefStep") == 0) {
			mb_LPDDR5X_1D[ps].TxVrefStep = value;
			shdw_LPDDR5X_1D[ps].TxVrefStep = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank0Byte0") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte0 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte0 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank0Byte1") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte1 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte1 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank0Byte2") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte2 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte2 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank0Byte3") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte3 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte3 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank1Byte0") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte0 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte0 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank1Byte1") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte1 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte1 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank1Byte2") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte2 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte2 = 1;
		} else if (strcmp(field, "RxDlyScanShiftRank1Byte3") == 0) {
			mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte3 = value;
			shdw_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte3 = 1;
		} else if (strcmp(field, "FCDfi0AcsmStartPS0") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS0 = value;
			shdw_LPDDR5X_1D[ps].FCDfi0AcsmStartPS0 = 1;
		} else if (strcmp(field, "FCDfi1AcsmStartPS0") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS0 = value;
			shdw_LPDDR5X_1D[ps].FCDfi1AcsmStartPS0 = 1;
		} else if (strcmp(field, "FCDfi0AcsmStartPS1") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS1 = value;
			shdw_LPDDR5X_1D[ps].FCDfi0AcsmStartPS1 = 1;
		} else if (strcmp(field, "FCDfi1AcsmStartPS1") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS1 = value;
			shdw_LPDDR5X_1D[ps].FCDfi1AcsmStartPS1 = 1;
		} else if (strcmp(field, "FCDfi0AcsmStartPS2") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS2 = value;
			shdw_LPDDR5X_1D[ps].FCDfi0AcsmStartPS2 = 1;
		} else if (strcmp(field, "FCDfi1AcsmStartPS2") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS2 = value;
			shdw_LPDDR5X_1D[ps].FCDfi1AcsmStartPS2 = 1;
		} else if (strcmp(field, "FCDfi0AcsmStartPS3") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS3 = value;
			shdw_LPDDR5X_1D[ps].FCDfi0AcsmStartPS3 = 1;
		} else if (strcmp(field, "FCDfi1AcsmStartPS3") == 0) {
			mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS3 = value;
			shdw_LPDDR5X_1D[ps].FCDfi1AcsmStartPS3 = 1;
		} else if (strcmp(field, "RdDQSBitTimeControl") == 0) {
			mb_LPDDR5X_1D[ps].RdDQSBitTimeControl = value;
			shdw_LPDDR5X_1D[ps].RdDQSBitTimeControl = 1;
		} else if (strcmp(field, "WrDqBitTimeControl") == 0) {
			mb_LPDDR5X_1D[ps].WrDqBitTimeControl = value;
			shdw_LPDDR5X_1D[ps].WrDqBitTimeControl = 1;
		} else if (strcmp(field, "VrefOffsetBitTimeControl") == 0) {
			mb_LPDDR5X_1D[ps].VrefOffsetBitTimeControl = value;
			shdw_LPDDR5X_1D[ps].VrefOffsetBitTimeControl = 1;
		} else if (strcmp(field, "PhyDCABitTimeControl") == 0) {
			mb_LPDDR5X_1D[ps].PhyDCABitTimeControl = value;
			shdw_LPDDR5X_1D[ps].PhyDCABitTimeControl = 1;
		} else if (strcmp(field, "RxDFEBitTimeControl") == 0) {
			mb_LPDDR5X_1D[ps].RxDFEBitTimeControl = value;
			shdw_LPDDR5X_1D[ps].RxDFEBitTimeControl = 1;
		} else if (strcmp(field, "TrainedDRAMDQ1DFE_A0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_A0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_A0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ2DFE_A0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_A0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_A0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ3DFE_A0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_A0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_A0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ4DFE_A0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_A0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_A0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ1DFE_A1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_A1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_A1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ2DFE_A1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_A1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_A1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ3DFE_A1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_A1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_A1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ4DFE_A1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_A1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_A1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ1DFE_B0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_B0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_B0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ2DFE_B0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_B0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_B0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ3DFE_B0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_B0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_B0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ4DFE_B0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_B0 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_B0 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ1DFE_B1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_B1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_B1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ2DFE_B1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_B1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_B1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ3DFE_B1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_B1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_B1 = 1;
		} else if (strcmp(field, "TrainedDRAMDQ4DFE_B1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_B1 = value;
			shdw_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_B1 = 1;
		} else if (strcmp(field, "DramSupport7StepDFE") == 0) {
			mb_LPDDR5X_1D[ps].DramSupport7StepDFE = value;
			shdw_LPDDR5X_1D[ps].DramSupport7StepDFE = 1;
		} else if (strcmp(field, "PhyEnhancedTxDCA") == 0) {
			mb_LPDDR5X_1D[ps].PhyEnhancedTxDCA = value;
			shdw_LPDDR5X_1D[ps].PhyEnhancedTxDCA = 1;
		} else if (strcmp(field, "TrainedRXDRAMDCA_A0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_A0 = value;
			shdw_LPDDR5X_1D[ps].TrainedRXDRAMDCA_A0 = 1;
		} else if (strcmp(field, "TrainedRXDRAMDCA_A1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_A1 = value;
			shdw_LPDDR5X_1D[ps].TrainedRXDRAMDCA_A1 = 1;
		} else if (strcmp(field, "TrainedRXDRAMDCA_B0") == 0) {
			mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_B0 = value;
			shdw_LPDDR5X_1D[ps].TrainedRXDRAMDCA_B0 = 1;
		} else if (strcmp(field, "TrainedRXDRAMDCA_B1") == 0) {
			mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_B1 = value;
			shdw_LPDDR5X_1D[ps].TrainedRXDRAMDCA_B1 = 1;
		} else if (strcmp(field, "RdDQSSiMinEyeWidth") == 0) {
			mb_LPDDR5X_1D[ps].RdDQSSiMinEyeWidth = value;
			shdw_LPDDR5X_1D[ps].RdDQSSiMinEyeWidth = 1;
		} else if (strcmp(field, "RdDQSPRBSMinEyeWidth") == 0) {
			mb_LPDDR5X_1D[ps].RdDQSPRBSMinEyeWidth = value;
			shdw_LPDDR5X_1D[ps].RdDQSPRBSMinEyeWidth = 1;
		} else if (strcmp(field, "TxDQMinEyeWidth") == 0) {
			mb_LPDDR5X_1D[ps].TxDQMinEyeWidth = value;
			shdw_LPDDR5X_1D[ps].TxDQMinEyeWidth = 1;
		} else if (strcmp(field, "CATrnMinEyeWidth") == 0) {
			mb_LPDDR5X_1D[ps].CATrnMinEyeWidth = value;
			shdw_LPDDR5X_1D[ps].CATrnMinEyeWidth = 1;
		} else if (strcmp(field, "SelfTest") == 0) {
			mb_LPDDR5X_1D[ps].SelfTest = value;
			shdw_LPDDR5X_1D[ps].SelfTest = 1;
		} else if (strcmp(field, "RxClk1uiMinFine") == 0) {
			mb_LPDDR5X_1D[ps].RxClk1uiMinFine = value;
			shdw_LPDDR5X_1D[ps].RxClk1uiMinFine = 1;
		} else if (strcmp(field, "Rx2UIThreshold") == 0) {
			mb_LPDDR5X_1D[ps].Rx2UIThreshold = value;
			shdw_LPDDR5X_1D[ps].Rx2UIThreshold = 1;
		} else if (strcmp(field, "Rx1UIThreshold") == 0) {
			mb_LPDDR5X_1D[ps].Rx1UIThreshold = value;
			shdw_LPDDR5X_1D[ps].Rx1UIThreshold = 1;
		} else if (strcmp(field, "QBCPllUPllProg0") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllUPllProg0 = value;
			shdw_LPDDR5X_1D[ps].QBCPllUPllProg0 = 1;
		} else if (strcmp(field, "QBCPllUPllProg1") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllUPllProg1 = value;
			shdw_LPDDR5X_1D[ps].QBCPllUPllProg1 = 1;
		} else if (strcmp(field, "QBCPllUPllProg2") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllUPllProg2 = value;
			shdw_LPDDR5X_1D[ps].QBCPllUPllProg2 = 1;
		} else if (strcmp(field, "QBCPllUPllProg3") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllUPllProg3 = value;
			shdw_LPDDR5X_1D[ps].QBCPllUPllProg3 = 1;
		} else if (strcmp(field, "QBCPllCtrl1Px") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllCtrl1Px = value;
			shdw_LPDDR5X_1D[ps].QBCPllCtrl1Px = 1;
		} else if (strcmp(field, "QBCPllCtrl4Px") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllCtrl4Px = value;
			shdw_LPDDR5X_1D[ps].QBCPllCtrl4Px = 1;
		} else if (strcmp(field, "QBCPllCtrl5Px") == 0) {
			mb_LPDDR5X_1D[ps].QBCPllCtrl5Px = value;
			shdw_LPDDR5X_1D[ps].QBCPllCtrl5Px = 1;
		} else if (strcmp(field, "Lp5xTinit3Op1") == 0) {
			mb_LPDDR5X_1D[ps].Lp5xTinit3Op1 = value;
			shdw_LPDDR5X_1D[ps].Lp5xTinit3Op1 = 1;
		} else if (strcmp(field, "Lp5xTinit3Op2") == 0) {
			mb_LPDDR5X_1D[ps].Lp5xTinit3Op2 = value;
			shdw_LPDDR5X_1D[ps].Lp5xTinit3Op2 = 1;
		} else if (strcmp(field, "VMRSControl") == 0) {
			mb_LPDDR5X_1D[ps].VMRSControl = value;
			shdw_LPDDR5X_1D[ps].VMRSControl = 1;
		} else if (strcmp(field, "VMRSCount") == 0) {
			mb_LPDDR5X_1D[ps].VMRSCount = value;
			shdw_LPDDR5X_1D[ps].VMRSCount = 1;
		} else if (strcmp(field, "VMRSAddr0") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr0 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr0 = 1;
		} else if (strcmp(field, "VMRSAddr1") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr1 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr1 = 1;
		} else if (strcmp(field, "VMRSAddr2") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr2 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr2 = 1;
		} else if (strcmp(field, "VMRSAddr3") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr3 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr3 = 1;
		} else if (strcmp(field, "VMRSAddr4") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr4 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr4 = 1;
		} else if (strcmp(field, "VMRSAddr5") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr5 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr5 = 1;
		} else if (strcmp(field, "VMRSAddr6") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr6 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr6 = 1;
		} else if (strcmp(field, "VMRSAddr7") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr7 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr7 = 1;
		} else if (strcmp(field, "VMRSAddr8") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr8 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr8 = 1;
		} else if (strcmp(field, "VMRSAddr9") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr9 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr9 = 1;
		} else if (strcmp(field, "VMRSAddr10") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr10 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr10 = 1;
		} else if (strcmp(field, "VMRSAddr11") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr11 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr11 = 1;
		} else if (strcmp(field, "VMRSAddr12") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr12 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr12 = 1;
		} else if (strcmp(field, "VMRSAddr13") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr13 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr13 = 1;
		} else if (strcmp(field, "VMRSAddr14") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr14 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr14 = 1;
		} else if (strcmp(field, "VMRSAddr15") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr15 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr15 = 1;
		} else if (strcmp(field, "VMRSAddr16") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr16 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr16 = 1;
		} else if (strcmp(field, "VMRSAddr17") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr17 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr17 = 1;
		} else if (strcmp(field, "VMRSAddr18") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr18 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr18 = 1;
		} else if (strcmp(field, "VMRSAddr19") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr19 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr19 = 1;
		} else if (strcmp(field, "VMRSAddr20") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr20 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr20 = 1;
		} else if (strcmp(field, "VMRSAddr21") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr21 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr21 = 1;
		} else if (strcmp(field, "VMRSAddr22") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr22 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr22 = 1;
		} else if (strcmp(field, "VMRSAddr23") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr23 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr23 = 1;
		} else if (strcmp(field, "VMRSAddr24") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr24 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr24 = 1;
		} else if (strcmp(field, "VMRSAddr25") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr25 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr25 = 1;
		} else if (strcmp(field, "VMRSAddr26") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr26 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr26 = 1;
		} else if (strcmp(field, "VMRSAddr27") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr27 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr27 = 1;
		} else if (strcmp(field, "VMRSAddr28") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr28 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr28 = 1;
		} else if (strcmp(field, "VMRSAddr29") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr29 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr29 = 1;
		} else if (strcmp(field, "VMRSAddr30") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr30 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr30 = 1;
		} else if (strcmp(field, "VMRSAddr31") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr31 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr31 = 1;
		} else if (strcmp(field, "VMRSAddr32") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr32 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr32 = 1;
		} else if (strcmp(field, "VMRSAddr33") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr33 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr33 = 1;
		} else if (strcmp(field, "VMRSAddr34") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr34 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr34 = 1;
		} else if (strcmp(field, "VMRSAddr35") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr35 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr35 = 1;
		} else if (strcmp(field, "VMRSAddr36") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr36 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr36 = 1;
		} else if (strcmp(field, "VMRSAddr37") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr37 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr37 = 1;
		} else if (strcmp(field, "VMRSAddr38") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr38 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr38 = 1;
		} else if (strcmp(field, "VMRSAddr39") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr39 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr39 = 1;
		} else if (strcmp(field, "VMRSAddr40") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr40 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr40 = 1;
		} else if (strcmp(field, "VMRSAddr41") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr41 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr41 = 1;
		} else if (strcmp(field, "VMRSAddr42") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr42 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr42 = 1;
		} else if (strcmp(field, "VMRSAddr43") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr43 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr43 = 1;
		} else if (strcmp(field, "VMRSAddr44") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr44 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr44 = 1;
		} else if (strcmp(field, "VMRSAddr45") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr45 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr45 = 1;
		} else if (strcmp(field, "VMRSAddr46") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr46 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr46 = 1;
		} else if (strcmp(field, "VMRSAddr47") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr47 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr47 = 1;
		} else if (strcmp(field, "VMRSAddr48") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr48 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr48 = 1;
		} else if (strcmp(field, "VMRSAddr49") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr49 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr49 = 1;
		} else if (strcmp(field, "VMRSAddr50") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr50 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr50 = 1;
		} else if (strcmp(field, "VMRSAddr51") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr51 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr51 = 1;
		} else if (strcmp(field, "VMRSAddr52") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr52 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr52 = 1;
		} else if (strcmp(field, "VMRSAddr53") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr53 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr53 = 1;
		} else if (strcmp(field, "VMRSAddr54") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr54 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr54 = 1;
		} else if (strcmp(field, "VMRSAddr55") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr55 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr55 = 1;
		} else if (strcmp(field, "VMRSAddr56") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr56 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr56 = 1;
		} else if (strcmp(field, "VMRSAddr57") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr57 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr57 = 1;
		} else if (strcmp(field, "VMRSAddr58") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr58 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr58 = 1;
		} else if (strcmp(field, "VMRSAddr59") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr59 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr59 = 1;
		} else if (strcmp(field, "VMRSAddr60") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr60 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr60 = 1;
		} else if (strcmp(field, "VMRSAddr61") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr61 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr61 = 1;
		} else if (strcmp(field, "VMRSAddr62") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr62 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr62 = 1;
		} else if (strcmp(field, "VMRSAddr63") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr63 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr63 = 1;
		} else if (strcmp(field, "VMRSAddr64") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr64 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr64 = 1;
		} else if (strcmp(field, "VMRSAddr65") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr65 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr65 = 1;
		} else if (strcmp(field, "VMRSAddr66") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr66 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr66 = 1;
		} else if (strcmp(field, "VMRSAddr67") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr67 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr67 = 1;
		} else if (strcmp(field, "VMRSAddr68") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr68 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr68 = 1;
		} else if (strcmp(field, "VMRSAddr69") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr69 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr69 = 1;
		} else if (strcmp(field, "VMRSAddr70") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr70 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr70 = 1;
		} else if (strcmp(field, "VMRSAddr71") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr71 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr71 = 1;
		} else if (strcmp(field, "VMRSAddr72") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr72 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr72 = 1;
		} else if (strcmp(field, "VMRSAddr73") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr73 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr73 = 1;
		} else if (strcmp(field, "VMRSAddr74") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr74 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr74 = 1;
		} else if (strcmp(field, "VMRSAddr75") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr75 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr75 = 1;
		} else if (strcmp(field, "VMRSAddr76") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr76 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr76 = 1;
		} else if (strcmp(field, "VMRSAddr77") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr77 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr77 = 1;
		} else if (strcmp(field, "VMRSAddr78") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr78 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr78 = 1;
		} else if (strcmp(field, "VMRSAddr79") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr79 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr79 = 1;
		} else if (strcmp(field, "VMRSAddr80") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr80 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr80 = 1;
		} else if (strcmp(field, "VMRSAddr81") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr81 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr81 = 1;
		} else if (strcmp(field, "VMRSAddr82") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr82 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr82 = 1;
		} else if (strcmp(field, "VMRSAddr83") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr83 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr83 = 1;
		} else if (strcmp(field, "VMRSAddr84") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr84 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr84 = 1;
		} else if (strcmp(field, "VMRSAddr85") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr85 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr85 = 1;
		} else if (strcmp(field, "VMRSAddr86") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr86 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr86 = 1;
		} else if (strcmp(field, "VMRSAddr87") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr87 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr87 = 1;
		} else if (strcmp(field, "VMRSAddr88") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr88 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr88 = 1;
		} else if (strcmp(field, "VMRSAddr89") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr89 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr89 = 1;
		} else if (strcmp(field, "VMRSAddr90") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr90 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr90 = 1;
		} else if (strcmp(field, "VMRSAddr91") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr91 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr91 = 1;
		} else if (strcmp(field, "VMRSAddr92") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr92 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr92 = 1;
		} else if (strcmp(field, "VMRSAddr93") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr93 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr93 = 1;
		} else if (strcmp(field, "VMRSAddr94") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr94 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr94 = 1;
		} else if (strcmp(field, "VMRSAddr95") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr95 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr95 = 1;
		} else if (strcmp(field, "VMRSAddr96") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr96 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr96 = 1;
		} else if (strcmp(field, "VMRSAddr97") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr97 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr97 = 1;
		} else if (strcmp(field, "VMRSAddr98") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr98 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr98 = 1;
		} else if (strcmp(field, "VMRSAddr99") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr99 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr99 = 1;
		} else if (strcmp(field, "VMRSAddr100") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr100 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr100 = 1;
		} else if (strcmp(field, "VMRSAddr101") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr101 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr101 = 1;
		} else if (strcmp(field, "VMRSAddr102") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr102 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr102 = 1;
		} else if (strcmp(field, "VMRSAddr103") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr103 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr103 = 1;
		} else if (strcmp(field, "VMRSAddr104") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr104 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr104 = 1;
		} else if (strcmp(field, "VMRSAddr105") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr105 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr105 = 1;
		} else if (strcmp(field, "VMRSAddr106") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr106 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr106 = 1;
		} else if (strcmp(field, "VMRSAddr107") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr107 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr107 = 1;
		} else if (strcmp(field, "VMRSAddr108") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr108 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr108 = 1;
		} else if (strcmp(field, "VMRSAddr109") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr109 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr109 = 1;
		} else if (strcmp(field, "VMRSAddr110") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr110 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr110 = 1;
		} else if (strcmp(field, "VMRSAddr111") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr111 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr111 = 1;
		} else if (strcmp(field, "VMRSAddr112") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr112 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr112 = 1;
		} else if (strcmp(field, "VMRSAddr113") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr113 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr113 = 1;
		} else if (strcmp(field, "VMRSAddr114") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr114 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr114 = 1;
		} else if (strcmp(field, "VMRSAddr115") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr115 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr115 = 1;
		} else if (strcmp(field, "VMRSAddr116") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr116 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr116 = 1;
		} else if (strcmp(field, "VMRSAddr117") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr117 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr117 = 1;
		} else if (strcmp(field, "VMRSAddr118") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr118 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr118 = 1;
		} else if (strcmp(field, "VMRSAddr119") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr119 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr119 = 1;
		} else if (strcmp(field, "VMRSAddr120") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr120 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr120 = 1;
		} else if (strcmp(field, "VMRSAddr121") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr121 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr121 = 1;
		} else if (strcmp(field, "VMRSAddr122") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr122 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr122 = 1;
		} else if (strcmp(field, "VMRSAddr123") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr123 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr123 = 1;
		} else if (strcmp(field, "VMRSAddr124") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr124 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr124 = 1;
		} else if (strcmp(field, "VMRSAddr125") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr125 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr125 = 1;
		} else if (strcmp(field, "VMRSAddr126") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr126 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr126 = 1;
		} else if (strcmp(field, "VMRSAddr127") == 0) {
			mb_LPDDR5X_1D[ps].VMRSAddr127 = value;
			shdw_LPDDR5X_1D[ps].VMRSAddr127 = 1;
		} else if (strcmp(field, "VMRSData0") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData0 = value;
			shdw_LPDDR5X_1D[ps].VMRSData0 = 1;
		} else if (strcmp(field, "VMRSData1") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData1 = value;
			shdw_LPDDR5X_1D[ps].VMRSData1 = 1;
		} else if (strcmp(field, "VMRSData2") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData2 = value;
			shdw_LPDDR5X_1D[ps].VMRSData2 = 1;
		} else if (strcmp(field, "VMRSData3") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData3 = value;
			shdw_LPDDR5X_1D[ps].VMRSData3 = 1;
		} else if (strcmp(field, "VMRSData4") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData4 = value;
			shdw_LPDDR5X_1D[ps].VMRSData4 = 1;
		} else if (strcmp(field, "VMRSData5") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData5 = value;
			shdw_LPDDR5X_1D[ps].VMRSData5 = 1;
		} else if (strcmp(field, "VMRSData6") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData6 = value;
			shdw_LPDDR5X_1D[ps].VMRSData6 = 1;
		} else if (strcmp(field, "VMRSData7") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData7 = value;
			shdw_LPDDR5X_1D[ps].VMRSData7 = 1;
		} else if (strcmp(field, "VMRSData8") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData8 = value;
			shdw_LPDDR5X_1D[ps].VMRSData8 = 1;
		} else if (strcmp(field, "VMRSData9") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData9 = value;
			shdw_LPDDR5X_1D[ps].VMRSData9 = 1;
		} else if (strcmp(field, "VMRSData10") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData10 = value;
			shdw_LPDDR5X_1D[ps].VMRSData10 = 1;
		} else if (strcmp(field, "VMRSData11") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData11 = value;
			shdw_LPDDR5X_1D[ps].VMRSData11 = 1;
		} else if (strcmp(field, "VMRSData12") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData12 = value;
			shdw_LPDDR5X_1D[ps].VMRSData12 = 1;
		} else if (strcmp(field, "VMRSData13") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData13 = value;
			shdw_LPDDR5X_1D[ps].VMRSData13 = 1;
		} else if (strcmp(field, "VMRSData14") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData14 = value;
			shdw_LPDDR5X_1D[ps].VMRSData14 = 1;
		} else if (strcmp(field, "VMRSData15") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData15 = value;
			shdw_LPDDR5X_1D[ps].VMRSData15 = 1;
		} else if (strcmp(field, "VMRSData16") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData16 = value;
			shdw_LPDDR5X_1D[ps].VMRSData16 = 1;
		} else if (strcmp(field, "VMRSData17") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData17 = value;
			shdw_LPDDR5X_1D[ps].VMRSData17 = 1;
		} else if (strcmp(field, "VMRSData18") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData18 = value;
			shdw_LPDDR5X_1D[ps].VMRSData18 = 1;
		} else if (strcmp(field, "VMRSData19") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData19 = value;
			shdw_LPDDR5X_1D[ps].VMRSData19 = 1;
		} else if (strcmp(field, "VMRSData20") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData20 = value;
			shdw_LPDDR5X_1D[ps].VMRSData20 = 1;
		} else if (strcmp(field, "VMRSData21") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData21 = value;
			shdw_LPDDR5X_1D[ps].VMRSData21 = 1;
		} else if (strcmp(field, "VMRSData22") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData22 = value;
			shdw_LPDDR5X_1D[ps].VMRSData22 = 1;
		} else if (strcmp(field, "VMRSData23") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData23 = value;
			shdw_LPDDR5X_1D[ps].VMRSData23 = 1;
		} else if (strcmp(field, "VMRSData24") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData24 = value;
			shdw_LPDDR5X_1D[ps].VMRSData24 = 1;
		} else if (strcmp(field, "VMRSData25") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData25 = value;
			shdw_LPDDR5X_1D[ps].VMRSData25 = 1;
		} else if (strcmp(field, "VMRSData26") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData26 = value;
			shdw_LPDDR5X_1D[ps].VMRSData26 = 1;
		} else if (strcmp(field, "VMRSData27") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData27 = value;
			shdw_LPDDR5X_1D[ps].VMRSData27 = 1;
		} else if (strcmp(field, "VMRSData28") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData28 = value;
			shdw_LPDDR5X_1D[ps].VMRSData28 = 1;
		} else if (strcmp(field, "VMRSData29") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData29 = value;
			shdw_LPDDR5X_1D[ps].VMRSData29 = 1;
		} else if (strcmp(field, "VMRSData30") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData30 = value;
			shdw_LPDDR5X_1D[ps].VMRSData30 = 1;
		} else if (strcmp(field, "VMRSData31") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData31 = value;
			shdw_LPDDR5X_1D[ps].VMRSData31 = 1;
		} else if (strcmp(field, "VMRSData32") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData32 = value;
			shdw_LPDDR5X_1D[ps].VMRSData32 = 1;
		} else if (strcmp(field, "VMRSData33") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData33 = value;
			shdw_LPDDR5X_1D[ps].VMRSData33 = 1;
		} else if (strcmp(field, "VMRSData34") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData34 = value;
			shdw_LPDDR5X_1D[ps].VMRSData34 = 1;
		} else if (strcmp(field, "VMRSData35") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData35 = value;
			shdw_LPDDR5X_1D[ps].VMRSData35 = 1;
		} else if (strcmp(field, "VMRSData36") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData36 = value;
			shdw_LPDDR5X_1D[ps].VMRSData36 = 1;
		} else if (strcmp(field, "VMRSData37") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData37 = value;
			shdw_LPDDR5X_1D[ps].VMRSData37 = 1;
		} else if (strcmp(field, "VMRSData38") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData38 = value;
			shdw_LPDDR5X_1D[ps].VMRSData38 = 1;
		} else if (strcmp(field, "VMRSData39") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData39 = value;
			shdw_LPDDR5X_1D[ps].VMRSData39 = 1;
		} else if (strcmp(field, "VMRSData40") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData40 = value;
			shdw_LPDDR5X_1D[ps].VMRSData40 = 1;
		} else if (strcmp(field, "VMRSData41") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData41 = value;
			shdw_LPDDR5X_1D[ps].VMRSData41 = 1;
		} else if (strcmp(field, "VMRSData42") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData42 = value;
			shdw_LPDDR5X_1D[ps].VMRSData42 = 1;
		} else if (strcmp(field, "VMRSData43") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData43 = value;
			shdw_LPDDR5X_1D[ps].VMRSData43 = 1;
		} else if (strcmp(field, "VMRSData44") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData44 = value;
			shdw_LPDDR5X_1D[ps].VMRSData44 = 1;
		} else if (strcmp(field, "VMRSData45") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData45 = value;
			shdw_LPDDR5X_1D[ps].VMRSData45 = 1;
		} else if (strcmp(field, "VMRSData46") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData46 = value;
			shdw_LPDDR5X_1D[ps].VMRSData46 = 1;
		} else if (strcmp(field, "VMRSData47") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData47 = value;
			shdw_LPDDR5X_1D[ps].VMRSData47 = 1;
		} else if (strcmp(field, "VMRSData48") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData48 = value;
			shdw_LPDDR5X_1D[ps].VMRSData48 = 1;
		} else if (strcmp(field, "VMRSData49") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData49 = value;
			shdw_LPDDR5X_1D[ps].VMRSData49 = 1;
		} else if (strcmp(field, "VMRSData50") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData50 = value;
			shdw_LPDDR5X_1D[ps].VMRSData50 = 1;
		} else if (strcmp(field, "VMRSData51") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData51 = value;
			shdw_LPDDR5X_1D[ps].VMRSData51 = 1;
		} else if (strcmp(field, "VMRSData52") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData52 = value;
			shdw_LPDDR5X_1D[ps].VMRSData52 = 1;
		} else if (strcmp(field, "VMRSData53") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData53 = value;
			shdw_LPDDR5X_1D[ps].VMRSData53 = 1;
		} else if (strcmp(field, "VMRSData54") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData54 = value;
			shdw_LPDDR5X_1D[ps].VMRSData54 = 1;
		} else if (strcmp(field, "VMRSData55") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData55 = value;
			shdw_LPDDR5X_1D[ps].VMRSData55 = 1;
		} else if (strcmp(field, "VMRSData56") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData56 = value;
			shdw_LPDDR5X_1D[ps].VMRSData56 = 1;
		} else if (strcmp(field, "VMRSData57") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData57 = value;
			shdw_LPDDR5X_1D[ps].VMRSData57 = 1;
		} else if (strcmp(field, "VMRSData58") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData58 = value;
			shdw_LPDDR5X_1D[ps].VMRSData58 = 1;
		} else if (strcmp(field, "VMRSData59") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData59 = value;
			shdw_LPDDR5X_1D[ps].VMRSData59 = 1;
		} else if (strcmp(field, "VMRSData60") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData60 = value;
			shdw_LPDDR5X_1D[ps].VMRSData60 = 1;
		} else if (strcmp(field, "VMRSData61") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData61 = value;
			shdw_LPDDR5X_1D[ps].VMRSData61 = 1;
		} else if (strcmp(field, "VMRSData62") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData62 = value;
			shdw_LPDDR5X_1D[ps].VMRSData62 = 1;
		} else if (strcmp(field, "VMRSData63") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData63 = value;
			shdw_LPDDR5X_1D[ps].VMRSData63 = 1;
		} else if (strcmp(field, "VMRSData64") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData64 = value;
			shdw_LPDDR5X_1D[ps].VMRSData64 = 1;
		} else if (strcmp(field, "VMRSData65") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData65 = value;
			shdw_LPDDR5X_1D[ps].VMRSData65 = 1;
		} else if (strcmp(field, "VMRSData66") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData66 = value;
			shdw_LPDDR5X_1D[ps].VMRSData66 = 1;
		} else if (strcmp(field, "VMRSData67") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData67 = value;
			shdw_LPDDR5X_1D[ps].VMRSData67 = 1;
		} else if (strcmp(field, "VMRSData68") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData68 = value;
			shdw_LPDDR5X_1D[ps].VMRSData68 = 1;
		} else if (strcmp(field, "VMRSData69") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData69 = value;
			shdw_LPDDR5X_1D[ps].VMRSData69 = 1;
		} else if (strcmp(field, "VMRSData70") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData70 = value;
			shdw_LPDDR5X_1D[ps].VMRSData70 = 1;
		} else if (strcmp(field, "VMRSData71") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData71 = value;
			shdw_LPDDR5X_1D[ps].VMRSData71 = 1;
		} else if (strcmp(field, "VMRSData72") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData72 = value;
			shdw_LPDDR5X_1D[ps].VMRSData72 = 1;
		} else if (strcmp(field, "VMRSData73") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData73 = value;
			shdw_LPDDR5X_1D[ps].VMRSData73 = 1;
		} else if (strcmp(field, "VMRSData74") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData74 = value;
			shdw_LPDDR5X_1D[ps].VMRSData74 = 1;
		} else if (strcmp(field, "VMRSData75") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData75 = value;
			shdw_LPDDR5X_1D[ps].VMRSData75 = 1;
		} else if (strcmp(field, "VMRSData76") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData76 = value;
			shdw_LPDDR5X_1D[ps].VMRSData76 = 1;
		} else if (strcmp(field, "VMRSData77") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData77 = value;
			shdw_LPDDR5X_1D[ps].VMRSData77 = 1;
		} else if (strcmp(field, "VMRSData78") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData78 = value;
			shdw_LPDDR5X_1D[ps].VMRSData78 = 1;
		} else if (strcmp(field, "VMRSData79") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData79 = value;
			shdw_LPDDR5X_1D[ps].VMRSData79 = 1;
		} else if (strcmp(field, "VMRSData80") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData80 = value;
			shdw_LPDDR5X_1D[ps].VMRSData80 = 1;
		} else if (strcmp(field, "VMRSData81") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData81 = value;
			shdw_LPDDR5X_1D[ps].VMRSData81 = 1;
		} else if (strcmp(field, "VMRSData82") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData82 = value;
			shdw_LPDDR5X_1D[ps].VMRSData82 = 1;
		} else if (strcmp(field, "VMRSData83") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData83 = value;
			shdw_LPDDR5X_1D[ps].VMRSData83 = 1;
		} else if (strcmp(field, "VMRSData84") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData84 = value;
			shdw_LPDDR5X_1D[ps].VMRSData84 = 1;
		} else if (strcmp(field, "VMRSData85") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData85 = value;
			shdw_LPDDR5X_1D[ps].VMRSData85 = 1;
		} else if (strcmp(field, "VMRSData86") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData86 = value;
			shdw_LPDDR5X_1D[ps].VMRSData86 = 1;
		} else if (strcmp(field, "VMRSData87") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData87 = value;
			shdw_LPDDR5X_1D[ps].VMRSData87 = 1;
		} else if (strcmp(field, "VMRSData88") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData88 = value;
			shdw_LPDDR5X_1D[ps].VMRSData88 = 1;
		} else if (strcmp(field, "VMRSData89") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData89 = value;
			shdw_LPDDR5X_1D[ps].VMRSData89 = 1;
		} else if (strcmp(field, "VMRSData90") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData90 = value;
			shdw_LPDDR5X_1D[ps].VMRSData90 = 1;
		} else if (strcmp(field, "VMRSData91") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData91 = value;
			shdw_LPDDR5X_1D[ps].VMRSData91 = 1;
		} else if (strcmp(field, "VMRSData92") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData92 = value;
			shdw_LPDDR5X_1D[ps].VMRSData92 = 1;
		} else if (strcmp(field, "VMRSData93") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData93 = value;
			shdw_LPDDR5X_1D[ps].VMRSData93 = 1;
		} else if (strcmp(field, "VMRSData94") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData94 = value;
			shdw_LPDDR5X_1D[ps].VMRSData94 = 1;
		} else if (strcmp(field, "VMRSData95") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData95 = value;
			shdw_LPDDR5X_1D[ps].VMRSData95 = 1;
		} else if (strcmp(field, "VMRSData96") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData96 = value;
			shdw_LPDDR5X_1D[ps].VMRSData96 = 1;
		} else if (strcmp(field, "VMRSData97") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData97 = value;
			shdw_LPDDR5X_1D[ps].VMRSData97 = 1;
		} else if (strcmp(field, "VMRSData98") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData98 = value;
			shdw_LPDDR5X_1D[ps].VMRSData98 = 1;
		} else if (strcmp(field, "VMRSData99") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData99 = value;
			shdw_LPDDR5X_1D[ps].VMRSData99 = 1;
		} else if (strcmp(field, "VMRSData100") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData100 = value;
			shdw_LPDDR5X_1D[ps].VMRSData100 = 1;
		} else if (strcmp(field, "VMRSData101") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData101 = value;
			shdw_LPDDR5X_1D[ps].VMRSData101 = 1;
		} else if (strcmp(field, "VMRSData102") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData102 = value;
			shdw_LPDDR5X_1D[ps].VMRSData102 = 1;
		} else if (strcmp(field, "VMRSData103") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData103 = value;
			shdw_LPDDR5X_1D[ps].VMRSData103 = 1;
		} else if (strcmp(field, "VMRSData104") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData104 = value;
			shdw_LPDDR5X_1D[ps].VMRSData104 = 1;
		} else if (strcmp(field, "VMRSData105") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData105 = value;
			shdw_LPDDR5X_1D[ps].VMRSData105 = 1;
		} else if (strcmp(field, "VMRSData106") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData106 = value;
			shdw_LPDDR5X_1D[ps].VMRSData106 = 1;
		} else if (strcmp(field, "VMRSData107") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData107 = value;
			shdw_LPDDR5X_1D[ps].VMRSData107 = 1;
		} else if (strcmp(field, "VMRSData108") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData108 = value;
			shdw_LPDDR5X_1D[ps].VMRSData108 = 1;
		} else if (strcmp(field, "VMRSData109") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData109 = value;
			shdw_LPDDR5X_1D[ps].VMRSData109 = 1;
		} else if (strcmp(field, "VMRSData110") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData110 = value;
			shdw_LPDDR5X_1D[ps].VMRSData110 = 1;
		} else if (strcmp(field, "VMRSData111") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData111 = value;
			shdw_LPDDR5X_1D[ps].VMRSData111 = 1;
		} else if (strcmp(field, "VMRSData112") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData112 = value;
			shdw_LPDDR5X_1D[ps].VMRSData112 = 1;
		} else if (strcmp(field, "VMRSData113") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData113 = value;
			shdw_LPDDR5X_1D[ps].VMRSData113 = 1;
		} else if (strcmp(field, "VMRSData114") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData114 = value;
			shdw_LPDDR5X_1D[ps].VMRSData114 = 1;
		} else if (strcmp(field, "VMRSData115") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData115 = value;
			shdw_LPDDR5X_1D[ps].VMRSData115 = 1;
		} else if (strcmp(field, "VMRSData116") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData116 = value;
			shdw_LPDDR5X_1D[ps].VMRSData116 = 1;
		} else if (strcmp(field, "VMRSData117") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData117 = value;
			shdw_LPDDR5X_1D[ps].VMRSData117 = 1;
		} else if (strcmp(field, "VMRSData118") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData118 = value;
			shdw_LPDDR5X_1D[ps].VMRSData118 = 1;
		} else if (strcmp(field, "VMRSData119") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData119 = value;
			shdw_LPDDR5X_1D[ps].VMRSData119 = 1;
		} else if (strcmp(field, "VMRSData120") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData120 = value;
			shdw_LPDDR5X_1D[ps].VMRSData120 = 1;
		} else if (strcmp(field, "VMRSData121") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData121 = value;
			shdw_LPDDR5X_1D[ps].VMRSData121 = 1;
		} else if (strcmp(field, "VMRSData122") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData122 = value;
			shdw_LPDDR5X_1D[ps].VMRSData122 = 1;
		} else if (strcmp(field, "VMRSData123") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData123 = value;
			shdw_LPDDR5X_1D[ps].VMRSData123 = 1;
		} else if (strcmp(field, "VMRSData124") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData124 = value;
			shdw_LPDDR5X_1D[ps].VMRSData124 = 1;
		} else if (strcmp(field, "VMRSData125") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData125 = value;
			shdw_LPDDR5X_1D[ps].VMRSData125 = 1;
		} else if (strcmp(field, "VMRSData126") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData126 = value;
			shdw_LPDDR5X_1D[ps].VMRSData126 = 1;
		} else if (strcmp(field, "VMRSData127") == 0) {
			mb_LPDDR5X_1D[ps].VMRSData127 = value;
			shdw_LPDDR5X_1D[ps].VMRSData127 = 1;
		} else {
			dwc_ddrphy_phyinit_assert(0, " [%s] unknown message block field name '%s', Train2D=%d\n", __func__, field, Train2D);
			return -1;
		}
	} else if (Train2D == 1) {
		/*
		 */
	} else {
		dwc_ddrphy_phyinit_assert(0, " [%s] invalid value for Train2D=%d\n", __func__, Train2D);
		return -3;
	}

	dwc_ddrphy_phyinit_cmnt(" [%s] Setting mb_LPDDR5X_%dD[%d].%s to 0x%x\n", __func__, Train2D + 1, ps, field, value);
	return 0;
}

/** @} */
