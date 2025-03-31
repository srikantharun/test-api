/** \file
 *  \brief Implements function to read messageBlock structure of PhyInit
 */

#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/**  \addtogroup SrcFunc
 *   @{
 */

/** @brief API to read the messageBlock structure in PhyInit.
 *
 *  This function can be used to read training firmware 1D/2D messageBlock fields
 *  for a given PState in the PhyInit Data structure.  As an example, to read MsgMsic to 0x4 for PState 3,
 *  for 1D Training :
 *  @code{.c}
 *  dwc_ddrphy_phyinit_setMB(3, "MsgMisc", 0x4, 0);
 *  @endcode
 *
 *  \note This functions doesn't read the DMEM address in SRAM. It returns
 *  what is programed in the PhyInit messageBlock structure which is used
 *  to write to the SRAM once dwc_ddrphy_phyinit_F_loadDMEM() is called in
 *  dwc_ddrphy_phyinit_sequence().
 *
 * @param[in]   phyctx  PhyInit context
 *
 * @param[in]   ps      integer between 0-3. Specifies the PState for which the
 * messageBlock field should be set.
 *
 * @param[in]   field   A string representing the messageBlock field to be
 * programed. refer to the messageBlock data structure for definition of fields
 * applicable to each protocol.
 *
 * @return field value on success. Returns following values based on
 * error:
 * - -1 : messageBlock field specified by the input \c field string is not
 * found in the messageBlock data structure.
 * - -2 : when DramType does not support 2D training but a 2D training field is
 * programmed.
 * - -3 : Train2D inputs is neither 1 or 0.
 */
int dwc_ddrphy_phyinit_getMb(phyinit_config_t *phyctx, int ps, char *field)
{
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	int Train2D = pRuntimeConfig->Train2D;
	PMU_SMB_LPDDR5X_1D_t *mb_LPDDR5X_1D = phyctx->mb_LPDDR5X_1D;

	if (Train2D == 0) {
		if (strcmp(field, "Reserved00") == 0) {
			return mb_LPDDR5X_1D[ps].Reserved00;
		}
		else if (strcmp(field, "MsgMisc") == 0) {
			return mb_LPDDR5X_1D[ps].MsgMisc;
		}
		else if (strcmp(field, "Pstate") == 0) {
			return mb_LPDDR5X_1D[ps].Pstate;
		}
		else if (strcmp(field, "PllBypassEn") == 0) {
			return mb_LPDDR5X_1D[ps].PllBypassEn;
		}
		else if (strcmp(field, "DRAMFreq") == 0) {
			return mb_LPDDR5X_1D[ps].DRAMFreq;
		}
		else if (strcmp(field, "DfiFreqRatio") == 0) {
			return mb_LPDDR5X_1D[ps].DfiFreqRatio;
		}
		else if (strcmp(field, "DcaOpts") == 0) {
			return mb_LPDDR5X_1D[ps].DcaOpts;
		}
		else if (strcmp(field, "Train2DMisc") == 0) {
			return mb_LPDDR5X_1D[ps].Train2DMisc;
		}
		else if (strcmp(field, "UseAltRxPath") == 0) {
			return mb_LPDDR5X_1D[ps].UseAltRxPath;
		}
		else if (strcmp(field, "Misc") == 0) {
			return mb_LPDDR5X_1D[ps].Misc;
		}
		else if (strcmp(field, "SIFriendlyDlyOffset") == 0) {
			return mb_LPDDR5X_1D[ps].SIFriendlyDlyOffset;
		}
		else if (strcmp(field, "SequenceCtrl") == 0) {
			return mb_LPDDR5X_1D[ps].SequenceCtrl;
		}
		else if (strcmp(field, "HdtCtrl") == 0) {
			return mb_LPDDR5X_1D[ps].HdtCtrl;
		}
		else if (strcmp(field, "Reserved13") == 0) {
			return mb_LPDDR5X_1D[ps].Reserved13;
		}
		else if (strcmp(field, "DFIMRLMargin") == 0) {
			return mb_LPDDR5X_1D[ps].DFIMRLMargin;
		}
		else if (strcmp(field, "TX2D_Delay_Weight") == 0) {
			return mb_LPDDR5X_1D[ps].TX2D_Delay_Weight;
		}
		else if (strcmp(field, "TX2D_Voltage_Weight") == 0) {
			return mb_LPDDR5X_1D[ps].TX2D_Voltage_Weight;
		}
		else if (strcmp(field, "Quickboot") == 0) {
			return mb_LPDDR5X_1D[ps].Quickboot;
		}
		else if (strcmp(field, "CaTrainAltUpdate") == 0) {
			return mb_LPDDR5X_1D[ps].CaTrainAltUpdate;
		}
		else if (strcmp(field, "CATrainOpt") == 0) {
			return mb_LPDDR5X_1D[ps].CATrainOpt;
		}
		else if (strcmp(field, "X8Mode") == 0) {
			return mb_LPDDR5X_1D[ps].X8Mode;
		}
		else if (strcmp(field, "RX2D_TrainOpt") == 0) {
			return mb_LPDDR5X_1D[ps].RX2D_TrainOpt;
		}
		else if (strcmp(field, "TX2D_TrainOpt") == 0) {
			return mb_LPDDR5X_1D[ps].TX2D_TrainOpt;
		}
		else if (strcmp(field, "RxDFEOpt") == 0) {
			return mb_LPDDR5X_1D[ps].RxDFEOpt;
		}
		else if (strcmp(field, "RX2D_Delay_Weight") == 0) {
			return mb_LPDDR5X_1D[ps].RX2D_Delay_Weight;
		}
		else if (strcmp(field, "RX2D_Voltage_Weight") == 0) {
			return mb_LPDDR5X_1D[ps].RX2D_Voltage_Weight;
		}
		else if (strcmp(field, "PhyConfigOverride") == 0) {
			return mb_LPDDR5X_1D[ps].PhyConfigOverride;
		}
		else if (strcmp(field, "EnabledDQsChA") == 0) {
			return mb_LPDDR5X_1D[ps].EnabledDQsChA;
		}
		else if (strcmp(field, "CsPresentChA") == 0) {
			return mb_LPDDR5X_1D[ps].CsPresentChA;
		}
		else if (strcmp(field, "CATerminatingRankChA") == 0) {
			return mb_LPDDR5X_1D[ps].CATerminatingRankChA;
		}
		else if (strcmp(field, "EnabledDQsChB") == 0) {
			return mb_LPDDR5X_1D[ps].EnabledDQsChB;
		}
		else if (strcmp(field, "CsPresentChB") == 0) {
			return mb_LPDDR5X_1D[ps].CsPresentChB;
		}
		else if (strcmp(field, "CATerminatingRankChB") == 0) {
			return mb_LPDDR5X_1D[ps].CATerminatingRankChB;
		}
		else if (strcmp(field, "MR1_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR1_A0;
		}
		else if (strcmp(field, "MR1_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR1_A1;
		}
		else if (strcmp(field, "MR1_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR1_B0;
		}
		else if (strcmp(field, "MR1_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR1_B1;
		}
		else if (strcmp(field, "MR2_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR2_A0;
		}
		else if (strcmp(field, "MR2_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR2_A1;
		}
		else if (strcmp(field, "MR2_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR2_B0;
		}
		else if (strcmp(field, "MR2_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR2_B1;
		}
		else if (strcmp(field, "MR3_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR3_A0;
		}
		else if (strcmp(field, "MR3_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR3_A1;
		}
		else if (strcmp(field, "MR3_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR3_B0;
		}
		else if (strcmp(field, "MR3_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR3_B1;
		}
		else if (strcmp(field, "MR10_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR10_A0;
		}
		else if (strcmp(field, "MR10_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR10_A1;
		}
		else if (strcmp(field, "MR10_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR10_B0;
		}
		else if (strcmp(field, "MR10_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR10_B1;
		}
		else if (strcmp(field, "MR11_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR11_A0;
		}
		else if (strcmp(field, "MR11_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR11_A1;
		}
		else if (strcmp(field, "MR11_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR11_B0;
		}
		else if (strcmp(field, "MR11_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR11_B1;
		}
		else if (strcmp(field, "MR12_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR12_A0;
		}
		else if (strcmp(field, "MR12_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR12_A1;
		}
		else if (strcmp(field, "MR12_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR12_B0;
		}
		else if (strcmp(field, "MR12_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR12_B1;
		}
		else if (strcmp(field, "MR13_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR13_A0;
		}
		else if (strcmp(field, "MR13_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR13_A1;
		}
		else if (strcmp(field, "MR13_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR13_B0;
		}
		else if (strcmp(field, "MR13_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR13_B1;
		}
		else if (strcmp(field, "MR14_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR14_A0;
		}
		else if (strcmp(field, "MR14_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR14_A1;
		}
		else if (strcmp(field, "MR14_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR14_B0;
		}
		else if (strcmp(field, "MR14_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR14_B1;
		}
		else if (strcmp(field, "MR15_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR15_A0;
		}
		else if (strcmp(field, "MR15_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR15_A1;
		}
		else if (strcmp(field, "MR15_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR15_B0;
		}
		else if (strcmp(field, "MR15_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR15_B1;
		}
		else if (strcmp(field, "MR16_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR16_A0;
		}
		else if (strcmp(field, "MR16_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR16_A1;
		}
		else if (strcmp(field, "MR16_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR16_B0;
		}
		else if (strcmp(field, "MR16_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR16_B1;
		}
		else if (strcmp(field, "MR17_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR17_A0;
		}
		else if (strcmp(field, "MR17_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR17_A1;
		}
		else if (strcmp(field, "MR17_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR17_B0;
		}
		else if (strcmp(field, "MR17_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR17_B1;
		}
		else if (strcmp(field, "MR18_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR18_A0;
		}
		else if (strcmp(field, "MR18_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR18_A1;
		}
		else if (strcmp(field, "MR18_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR18_B0;
		}
		else if (strcmp(field, "MR18_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR18_B1;
		}
		else if (strcmp(field, "MR19_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR19_A0;
		}
		else if (strcmp(field, "MR19_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR19_A1;
		}
		else if (strcmp(field, "MR19_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR19_B0;
		}
		else if (strcmp(field, "MR19_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR19_B1;
		}
		else if (strcmp(field, "MR20_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR20_A0;
		}
		else if (strcmp(field, "MR20_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR20_A1;
		}
		else if (strcmp(field, "MR20_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR20_B0;
		}
		else if (strcmp(field, "MR20_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR20_B1;
		}
		else if (strcmp(field, "MR21_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR21_A0;
		}
		else if (strcmp(field, "MR21_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR21_A1;
		}
		else if (strcmp(field, "MR21_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR21_B0;
		}
		else if (strcmp(field, "MR21_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR21_B1;
		}
		else if (strcmp(field, "MR22_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR22_A0;
		}
		else if (strcmp(field, "MR22_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR22_A1;
		}
		else if (strcmp(field, "MR22_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR22_B0;
		}
		else if (strcmp(field, "MR22_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR22_B1;
		}
		else if (strcmp(field, "MR24_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR24_A0;
		}
		else if (strcmp(field, "MR24_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR24_A1;
		}
		else if (strcmp(field, "MR24_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR24_B0;
		}
		else if (strcmp(field, "MR24_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR24_B1;
		}
		else if (strcmp(field, "MR25_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR25_A0;
		}
		else if (strcmp(field, "MR25_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR25_A1;
		}
		else if (strcmp(field, "MR25_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR25_B0;
		}
		else if (strcmp(field, "MR25_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR25_B1;
		}
		else if (strcmp(field, "MR26_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR26_A0;
		}
		else if (strcmp(field, "MR26_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR26_A1;
		}
		else if (strcmp(field, "MR26_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR26_B0;
		}
		else if (strcmp(field, "MR26_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR26_B1;
		}
		else if (strcmp(field, "MR27_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR27_A0;
		}
		else if (strcmp(field, "MR27_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR27_A1;
		}
		else if (strcmp(field, "MR27_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR27_B0;
		}
		else if (strcmp(field, "MR27_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR27_B1;
		}
		else if (strcmp(field, "MR28_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR28_A0;
		}
		else if (strcmp(field, "MR28_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR28_A1;
		}
		else if (strcmp(field, "MR28_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR28_B0;
		}
		else if (strcmp(field, "MR28_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR28_B1;
		}
		else if (strcmp(field, "MR30_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR30_A0;
		}
		else if (strcmp(field, "MR30_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR30_A1;
		}
		else if (strcmp(field, "MR30_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR30_B0;
		}
		else if (strcmp(field, "MR30_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR30_B1;
		}
		else if (strcmp(field, "MR31_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR31_A0;
		}
		else if (strcmp(field, "MR31_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR31_A1;
		}
		else if (strcmp(field, "MR31_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR31_B0;
		}
		else if (strcmp(field, "MR31_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR31_B1;
		}
		else if (strcmp(field, "MR32_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR32_A0;
		}
		else if (strcmp(field, "MR32_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR32_A1;
		}
		else if (strcmp(field, "MR32_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR32_B0;
		}
		else if (strcmp(field, "MR32_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR32_B1;
		}
		else if (strcmp(field, "MR33_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR33_A0;
		}
		else if (strcmp(field, "MR33_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR33_A1;
		}
		else if (strcmp(field, "MR33_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR33_B0;
		}
		else if (strcmp(field, "MR33_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR33_B1;
		}
		else if (strcmp(field, "MR34_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR34_A0;
		}
		else if (strcmp(field, "MR34_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR34_A1;
		}
		else if (strcmp(field, "MR34_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR34_B0;
		}
		else if (strcmp(field, "MR34_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR34_B1;
		}
		else if (strcmp(field, "MR37_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR37_A0;
		}
		else if (strcmp(field, "MR37_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR37_A1;
		}
		else if (strcmp(field, "MR37_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR37_B0;
		}
		else if (strcmp(field, "MR37_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR37_B1;
		}
		else if (strcmp(field, "MR40_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR40_A0;
		}
		else if (strcmp(field, "MR40_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR40_A1;
		}
		else if (strcmp(field, "MR40_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR40_B0;
		}
		else if (strcmp(field, "MR40_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR40_B1;
		}
		else if (strcmp(field, "MR41_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR41_A0;
		}
		else if (strcmp(field, "MR41_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR41_A1;
		}
		else if (strcmp(field, "MR41_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR41_B0;
		}
		else if (strcmp(field, "MR41_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR41_B1;
		}
		else if (strcmp(field, "MR57_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR57_A0;
		}
		else if (strcmp(field, "MR57_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR57_A1;
		}
		else if (strcmp(field, "MR57_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR57_B0;
		}
		else if (strcmp(field, "MR57_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR57_B1;
		}
		else if (strcmp(field, "MR58_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR58_A0;
		}
		else if (strcmp(field, "MR58_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR58_A1;
		}
		else if (strcmp(field, "MR58_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR58_B0;
		}
		else if (strcmp(field, "MR58_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR58_B1;
		}
		else if (strcmp(field, "MR69_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR69_A0;
		}
		else if (strcmp(field, "MR69_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR69_A1;
		}
		else if (strcmp(field, "MR69_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR69_B0;
		}
		else if (strcmp(field, "MR69_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR69_B1;
		}
		else if (strcmp(field, "MR70_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR70_A0;
		}
		else if (strcmp(field, "MR70_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR70_A1;
		}
		else if (strcmp(field, "MR70_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR70_B0;
		}
		else if (strcmp(field, "MR70_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR70_B1;
		}
		else if (strcmp(field, "MR71_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR71_A0;
		}
		else if (strcmp(field, "MR71_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR71_A1;
		}
		else if (strcmp(field, "MR71_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR71_B0;
		}
		else if (strcmp(field, "MR71_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR71_B1;
		}
		else if (strcmp(field, "MR72_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR72_A0;
		}
		else if (strcmp(field, "MR72_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR72_A1;
		}
		else if (strcmp(field, "MR72_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR72_B0;
		}
		else if (strcmp(field, "MR72_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR72_B1;
		}
		else if (strcmp(field, "MR73_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR73_A0;
		}
		else if (strcmp(field, "MR73_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR73_A1;
		}
		else if (strcmp(field, "MR73_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR73_B0;
		}
		else if (strcmp(field, "MR73_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR73_B1;
		}
		else if (strcmp(field, "MR74_A0") == 0) {
			return mb_LPDDR5X_1D[ps].MR74_A0;
		}
		else if (strcmp(field, "MR74_A1") == 0) {
			return mb_LPDDR5X_1D[ps].MR74_A1;
		}
		else if (strcmp(field, "MR74_B0") == 0) {
			return mb_LPDDR5X_1D[ps].MR74_B0;
		}
		else if (strcmp(field, "MR74_B1") == 0) {
			return mb_LPDDR5X_1D[ps].MR74_B1;
		}
		else if (strcmp(field, "Disable2D") == 0) {
			return mb_LPDDR5X_1D[ps].Disable2D;
		}
		else if (strcmp(field, "PPT2OffsetMargin") == 0) {
			return mb_LPDDR5X_1D[ps].PPT2OffsetMargin;
		}
		else if (strcmp(field, "forceRxReplica") == 0) {
			return mb_LPDDR5X_1D[ps].forceRxReplica;
		}
		else if (strcmp(field, "HardwareScans") == 0) {
			return mb_LPDDR5X_1D[ps].HardwareScans;
		}
		else if (strcmp(field, "TxDFETrainOpt") == 0) {
			return mb_LPDDR5X_1D[ps].TxDFETrainOpt;
		}
		else if (strcmp(field, "SDOpt") == 0) {
			return mb_LPDDR5X_1D[ps].SDOpt;
		}
		else if (strcmp(field, "RdWrPatternA") == 0) {
			return mb_LPDDR5X_1D[ps].RdWrPatternA;
		}
		else if (strcmp(field, "RdWrPatternB") == 0) {
			return mb_LPDDR5X_1D[ps].RdWrPatternB;
		}
		else if (strcmp(field, "RdWrInvert") == 0) {
			return mb_LPDDR5X_1D[ps].RdWrInvert;
		}
		else if (strcmp(field, "LdffMode") == 0) {
			return mb_LPDDR5X_1D[ps].LdffMode;
		}
		else if (strcmp(field, "FCDfi0AcsmStart") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi0AcsmStart;
		}
		else if (strcmp(field, "FCDfi1AcsmStart") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi1AcsmStart;
		}
		else if (strcmp(field, "FCDfi0AcsmStartPSY") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPSY;
		}
		else if (strcmp(field, "FCDfi1AcsmStartPSY") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPSY;
		}
		else if (strcmp(field, "FCDMAStartMR") == 0) {
			return mb_LPDDR5X_1D[ps].FCDMAStartMR;
		}
		else if (strcmp(field, "FCDMAStartCsr") == 0) {
			return mb_LPDDR5X_1D[ps].FCDMAStartCsr;
		}
		else if (strcmp(field, "EnCustomSettings") == 0) {
			return mb_LPDDR5X_1D[ps].EnCustomSettings;
		}
		else if (strcmp(field, "LSTxSlewCK") == 0) {
			return mb_LPDDR5X_1D[ps].LSTxSlewCK;
		}
		else if (strcmp(field, "LSTxSlewCS") == 0) {
			return mb_LPDDR5X_1D[ps].LSTxSlewCS;
		}
		else if (strcmp(field, "LSTxSlewCA") == 0) {
			return mb_LPDDR5X_1D[ps].LSTxSlewCA;
		}
		else if (strcmp(field, "LSTxImpedanceCK") == 0) {
			return mb_LPDDR5X_1D[ps].LSTxImpedanceCK;
		}
		else if (strcmp(field, "LSTxImpedanceCS") == 0) {
			return mb_LPDDR5X_1D[ps].LSTxImpedanceCS;
		}
		else if (strcmp(field, "LSTxImpedanceCA") == 0) {
			return mb_LPDDR5X_1D[ps].LSTxImpedanceCA;
		}
		else if (strcmp(field, "VrefFilterAboveVal") == 0) {
			return mb_LPDDR5X_1D[ps].VrefFilterAboveVal;
		}
		else if (strcmp(field, "VrefFilterBelowVal") == 0) {
			return mb_LPDDR5X_1D[ps].VrefFilterBelowVal;
		}
		else if (strcmp(field, "EMOpt") == 0) {
			return mb_LPDDR5X_1D[ps].EMOpt;
		}
		else if (strcmp(field, "VrefInc") == 0) {
			return mb_LPDDR5X_1D[ps].VrefInc;
		}
		else if (strcmp(field, "UpperLowerByte") == 0) {
			return mb_LPDDR5X_1D[ps].UpperLowerByte;
		}
		else if (strcmp(field, "ALT_RL") == 0) {
			return mb_LPDDR5X_1D[ps].ALT_RL;
		}
		else if (strcmp(field, "MAIN_RL") == 0) {
			return mb_LPDDR5X_1D[ps].MAIN_RL;
		}
		else if (strcmp(field, "CSBACKOFF") == 0) {
			return mb_LPDDR5X_1D[ps].CSBACKOFF;
		}
		else if (strcmp(field, "WrLvlTrainOpt") == 0) {
			return mb_LPDDR5X_1D[ps].WrLvlTrainOpt;
		}
		else if (strcmp(field, "MRLCalcAdj") == 0) {
			return mb_LPDDR5X_1D[ps].MRLCalcAdj;
		}
		else if (strcmp(field, "LP5XMode") == 0) {
			return mb_LPDDR5X_1D[ps].LP5XMode;
		}
		else if (strcmp(field, "RxVrefStartPat") == 0) {
			return mb_LPDDR5X_1D[ps].RxVrefStartPat;
		}
		else if (strcmp(field, "RxVrefStartPrbs") == 0) {
			return mb_LPDDR5X_1D[ps].RxVrefStartPrbs;
		}
		else if (strcmp(field, "RxVrefEndPat") == 0) {
			return mb_LPDDR5X_1D[ps].RxVrefEndPat;
		}
		else if (strcmp(field, "RxVrefEndPrbs") == 0) {
			return mb_LPDDR5X_1D[ps].RxVrefEndPrbs;
		}
		else if (strcmp(field, "TxVrefStart") == 0) {
			return mb_LPDDR5X_1D[ps].TxVrefStart;
		}
		else if (strcmp(field, "TxVrefEnd") == 0) {
			return mb_LPDDR5X_1D[ps].TxVrefEnd;
		}
		else if (strcmp(field, "RxVrefStepPat") == 0) {
			return mb_LPDDR5X_1D[ps].RxVrefStepPat;
		}
		else if (strcmp(field, "RxVrefStepPrbs") == 0) {
			return mb_LPDDR5X_1D[ps].RxVrefStepPrbs;
		}
		else if (strcmp(field, "TxVrefStep") == 0) {
			return mb_LPDDR5X_1D[ps].TxVrefStep;
		}
		else if (strcmp(field, "RxDlyScanShiftRank0Byte0") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte0;
		}
		else if (strcmp(field, "RxDlyScanShiftRank0Byte1") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte1;
		}
		else if (strcmp(field, "RxDlyScanShiftRank0Byte2") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte2;
		}
		else if (strcmp(field, "RxDlyScanShiftRank0Byte3") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank0Byte3;
		}
		else if (strcmp(field, "RxDlyScanShiftRank1Byte0") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte0;
		}
		else if (strcmp(field, "RxDlyScanShiftRank1Byte1") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte1;
		}
		else if (strcmp(field, "RxDlyScanShiftRank1Byte2") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte2;
		}
		else if (strcmp(field, "RxDlyScanShiftRank1Byte3") == 0) {
			return mb_LPDDR5X_1D[ps].RxDlyScanShiftRank1Byte3;
		}
		else if (strcmp(field, "FCDfi0AcsmStartPS0") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS0;
		}
		else if (strcmp(field, "FCDfi1AcsmStartPS0") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS0;
		}
		else if (strcmp(field, "FCDfi0AcsmStartPS1") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS1;
		}
		else if (strcmp(field, "FCDfi1AcsmStartPS1") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS1;
		}
		else if (strcmp(field, "FCDfi0AcsmStartPS2") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS2;
		}
		else if (strcmp(field, "FCDfi1AcsmStartPS2") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS2;
		}
		else if (strcmp(field, "FCDfi0AcsmStartPS3") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi0AcsmStartPS3;
		}
		else if (strcmp(field, "FCDfi1AcsmStartPS3") == 0) {
			return mb_LPDDR5X_1D[ps].FCDfi1AcsmStartPS3;
		}
		else if (strcmp(field, "RdDQSBitTimeControl") == 0) {
			return mb_LPDDR5X_1D[ps].RdDQSBitTimeControl;
		}
		else if (strcmp(field, "WrDqBitTimeControl") == 0) {
			return mb_LPDDR5X_1D[ps].WrDqBitTimeControl;
		}
		else if (strcmp(field, "VrefOffsetBitTimeControl") == 0) {
			return mb_LPDDR5X_1D[ps].VrefOffsetBitTimeControl;
		}
		else if (strcmp(field, "PhyDCABitTimeControl") == 0) {
			return mb_LPDDR5X_1D[ps].PhyDCABitTimeControl;
		}
		else if (strcmp(field, "RxDFEBitTimeControl") == 0) {
			return mb_LPDDR5X_1D[ps].RxDFEBitTimeControl;
		}
		else if (strcmp(field, "TrainedDRAMDQ1DFE_A0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_A0;
		}
		else if (strcmp(field, "TrainedDRAMDQ2DFE_A0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_A0;
		}
		else if (strcmp(field, "TrainedDRAMDQ3DFE_A0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_A0;
		}
		else if (strcmp(field, "TrainedDRAMDQ4DFE_A0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_A0;
		}
		else if (strcmp(field, "TrainedDRAMDQ1DFE_A1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_A1;
		}
		else if (strcmp(field, "TrainedDRAMDQ2DFE_A1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_A1;
		}
		else if (strcmp(field, "TrainedDRAMDQ3DFE_A1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_A1;
		}
		else if (strcmp(field, "TrainedDRAMDQ4DFE_A1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_A1;
		}
		else if (strcmp(field, "TrainedDRAMDQ1DFE_B0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_B0;
		}
		else if (strcmp(field, "TrainedDRAMDQ2DFE_B0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_B0;
		}
		else if (strcmp(field, "TrainedDRAMDQ3DFE_B0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_B0;
		}
		else if (strcmp(field, "TrainedDRAMDQ4DFE_B0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_B0;
		}
		else if (strcmp(field, "TrainedDRAMDQ1DFE_B1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ1DFE_B1;
		}
		else if (strcmp(field, "TrainedDRAMDQ2DFE_B1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ2DFE_B1;
		}
		else if (strcmp(field, "TrainedDRAMDQ3DFE_B1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ3DFE_B1;
		}
		else if (strcmp(field, "TrainedDRAMDQ4DFE_B1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedDRAMDQ4DFE_B1;
		}
		else if (strcmp(field, "DramSupport7StepDFE") == 0) {
			return mb_LPDDR5X_1D[ps].DramSupport7StepDFE;
		}
		else if (strcmp(field, "PhyEnhancedTxDCA") == 0) {
			return mb_LPDDR5X_1D[ps].PhyEnhancedTxDCA;
		}
		else if (strcmp(field, "TrainedRXDRAMDCA_A0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_A0;
		}
		else if (strcmp(field, "TrainedRXDRAMDCA_A1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_A1;
		}
		else if (strcmp(field, "TrainedRXDRAMDCA_B0") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_B0;
		}
		else if (strcmp(field, "TrainedRXDRAMDCA_B1") == 0) {
			return mb_LPDDR5X_1D[ps].TrainedRXDRAMDCA_B1;
		}
		else if (strcmp(field, "RdDQSSiMinEyeWidth") == 0) {
			return mb_LPDDR5X_1D[ps].RdDQSSiMinEyeWidth;
		}
		else if (strcmp(field, "RdDQSPRBSMinEyeWidth") == 0) {
			return mb_LPDDR5X_1D[ps].RdDQSPRBSMinEyeWidth;
		}
		else if (strcmp(field, "TxDQMinEyeWidth") == 0) {
			return mb_LPDDR5X_1D[ps].TxDQMinEyeWidth;
		}
		else if (strcmp(field, "CATrnMinEyeWidth") == 0) {
			return mb_LPDDR5X_1D[ps].CATrnMinEyeWidth;
		}
		else if (strcmp(field, "SelfTest") == 0) {
			return mb_LPDDR5X_1D[ps].SelfTest;
		}
		else if (strcmp(field, "RxClk1uiMinFine") == 0) {
			return mb_LPDDR5X_1D[ps].RxClk1uiMinFine;
		}
		else if (strcmp(field, "Rx2UIThreshold") == 0) {
			return mb_LPDDR5X_1D[ps].Rx2UIThreshold;
		}
		else if (strcmp(field, "Rx1UIThreshold") == 0) {
			return mb_LPDDR5X_1D[ps].Rx1UIThreshold;
		}
		else if (strcmp(field, "QBCPllUPllProg0") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllUPllProg0;
		}
		else if (strcmp(field, "QBCPllUPllProg1") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllUPllProg1;
		}
		else if (strcmp(field, "QBCPllUPllProg2") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllUPllProg2;
		}
		else if (strcmp(field, "QBCPllUPllProg3") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllUPllProg3;
		}
		else if (strcmp(field, "QBCPllCtrl1Px") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllCtrl1Px;
		}
		else if (strcmp(field, "QBCPllCtrl4Px") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllCtrl4Px;
		}
		else if (strcmp(field, "QBCPllCtrl5Px") == 0) {
			return mb_LPDDR5X_1D[ps].QBCPllCtrl5Px;
		}
		else if (strcmp(field, "Lp5xTinit3Op1") == 0) {
			return mb_LPDDR5X_1D[ps].Lp5xTinit3Op1;
		}
		else if (strcmp(field, "Lp5xTinit3Op2") == 0) {
			return mb_LPDDR5X_1D[ps].Lp5xTinit3Op2;
		}
		else if (strcmp(field, "VMRSControl") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSControl;
		}
		else if (strcmp(field, "VMRSCount") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSCount;
		}
		else if (strcmp(field, "VMRSAddr0") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr0;
		}
		else if (strcmp(field, "VMRSAddr1") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr1;
		}
		else if (strcmp(field, "VMRSAddr2") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr2;
		}
		else if (strcmp(field, "VMRSAddr3") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr3;
		}
		else if (strcmp(field, "VMRSAddr4") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr4;
		}
		else if (strcmp(field, "VMRSAddr5") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr5;
		}
		else if (strcmp(field, "VMRSAddr6") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr6;
		}
		else if (strcmp(field, "VMRSAddr7") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr7;
		}
		else if (strcmp(field, "VMRSAddr8") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr8;
		}
		else if (strcmp(field, "VMRSAddr9") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr9;
		}
		else if (strcmp(field, "VMRSAddr10") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr10;
		}
		else if (strcmp(field, "VMRSAddr11") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr11;
		}
		else if (strcmp(field, "VMRSAddr12") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr12;
		}
		else if (strcmp(field, "VMRSAddr13") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr13;
		}
		else if (strcmp(field, "VMRSAddr14") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr14;
		}
		else if (strcmp(field, "VMRSAddr15") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr15;
		}
		else if (strcmp(field, "VMRSAddr16") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr16;
		}
		else if (strcmp(field, "VMRSAddr17") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr17;
		}
		else if (strcmp(field, "VMRSAddr18") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr18;
		}
		else if (strcmp(field, "VMRSAddr19") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr19;
		}
		else if (strcmp(field, "VMRSAddr20") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr20;
		}
		else if (strcmp(field, "VMRSAddr21") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr21;
		}
		else if (strcmp(field, "VMRSAddr22") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr22;
		}
		else if (strcmp(field, "VMRSAddr23") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr23;
		}
		else if (strcmp(field, "VMRSAddr24") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr24;
		}
		else if (strcmp(field, "VMRSAddr25") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr25;
		}
		else if (strcmp(field, "VMRSAddr26") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr26;
		}
		else if (strcmp(field, "VMRSAddr27") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr27;
		}
		else if (strcmp(field, "VMRSAddr28") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr28;
		}
		else if (strcmp(field, "VMRSAddr29") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr29;
		}
		else if (strcmp(field, "VMRSAddr30") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr30;
		}
		else if (strcmp(field, "VMRSAddr31") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr31;
		}
		else if (strcmp(field, "VMRSAddr32") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr32;
		}
		else if (strcmp(field, "VMRSAddr33") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr33;
		}
		else if (strcmp(field, "VMRSAddr34") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr34;
		}
		else if (strcmp(field, "VMRSAddr35") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr35;
		}
		else if (strcmp(field, "VMRSAddr36") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr36;
		}
		else if (strcmp(field, "VMRSAddr37") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr37;
		}
		else if (strcmp(field, "VMRSAddr38") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr38;
		}
		else if (strcmp(field, "VMRSAddr39") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr39;
		}
		else if (strcmp(field, "VMRSAddr40") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr40;
		}
		else if (strcmp(field, "VMRSAddr41") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr41;
		}
		else if (strcmp(field, "VMRSAddr42") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr42;
		}
		else if (strcmp(field, "VMRSAddr43") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr43;
		}
		else if (strcmp(field, "VMRSAddr44") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr44;
		}
		else if (strcmp(field, "VMRSAddr45") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr45;
		}
		else if (strcmp(field, "VMRSAddr46") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr46;
		}
		else if (strcmp(field, "VMRSAddr47") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr47;
		}
		else if (strcmp(field, "VMRSAddr48") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr48;
		}
		else if (strcmp(field, "VMRSAddr49") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr49;
		}
		else if (strcmp(field, "VMRSAddr50") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr50;
		}
		else if (strcmp(field, "VMRSAddr51") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr51;
		}
		else if (strcmp(field, "VMRSAddr52") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr52;
		}
		else if (strcmp(field, "VMRSAddr53") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr53;
		}
		else if (strcmp(field, "VMRSAddr54") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr54;
		}
		else if (strcmp(field, "VMRSAddr55") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr55;
		}
		else if (strcmp(field, "VMRSAddr56") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr56;
		}
		else if (strcmp(field, "VMRSAddr57") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr57;
		}
		else if (strcmp(field, "VMRSAddr58") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr58;
		}
		else if (strcmp(field, "VMRSAddr59") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr59;
		}
		else if (strcmp(field, "VMRSAddr60") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr60;
		}
		else if (strcmp(field, "VMRSAddr61") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr61;
		}
		else if (strcmp(field, "VMRSAddr62") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr62;
		}
		else if (strcmp(field, "VMRSAddr63") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr63;
		}
		else if (strcmp(field, "VMRSAddr64") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr64;
		}
		else if (strcmp(field, "VMRSAddr65") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr65;
		}
		else if (strcmp(field, "VMRSAddr66") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr66;
		}
		else if (strcmp(field, "VMRSAddr67") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr67;
		}
		else if (strcmp(field, "VMRSAddr68") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr68;
		}
		else if (strcmp(field, "VMRSAddr69") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr69;
		}
		else if (strcmp(field, "VMRSAddr70") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr70;
		}
		else if (strcmp(field, "VMRSAddr71") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr71;
		}
		else if (strcmp(field, "VMRSAddr72") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr72;
		}
		else if (strcmp(field, "VMRSAddr73") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr73;
		}
		else if (strcmp(field, "VMRSAddr74") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr74;
		}
		else if (strcmp(field, "VMRSAddr75") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr75;
		}
		else if (strcmp(field, "VMRSAddr76") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr76;
		}
		else if (strcmp(field, "VMRSAddr77") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr77;
		}
		else if (strcmp(field, "VMRSAddr78") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr78;
		}
		else if (strcmp(field, "VMRSAddr79") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr79;
		}
		else if (strcmp(field, "VMRSAddr80") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr80;
		}
		else if (strcmp(field, "VMRSAddr81") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr81;
		}
		else if (strcmp(field, "VMRSAddr82") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr82;
		}
		else if (strcmp(field, "VMRSAddr83") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr83;
		}
		else if (strcmp(field, "VMRSAddr84") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr84;
		}
		else if (strcmp(field, "VMRSAddr85") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr85;
		}
		else if (strcmp(field, "VMRSAddr86") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr86;
		}
		else if (strcmp(field, "VMRSAddr87") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr87;
		}
		else if (strcmp(field, "VMRSAddr88") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr88;
		}
		else if (strcmp(field, "VMRSAddr89") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr89;
		}
		else if (strcmp(field, "VMRSAddr90") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr90;
		}
		else if (strcmp(field, "VMRSAddr91") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr91;
		}
		else if (strcmp(field, "VMRSAddr92") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr92;
		}
		else if (strcmp(field, "VMRSAddr93") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr93;
		}
		else if (strcmp(field, "VMRSAddr94") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr94;
		}
		else if (strcmp(field, "VMRSAddr95") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr95;
		}
		else if (strcmp(field, "VMRSAddr96") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr96;
		}
		else if (strcmp(field, "VMRSAddr97") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr97;
		}
		else if (strcmp(field, "VMRSAddr98") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr98;
		}
		else if (strcmp(field, "VMRSAddr99") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr99;
		}
		else if (strcmp(field, "VMRSAddr100") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr100;
		}
		else if (strcmp(field, "VMRSAddr101") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr101;
		}
		else if (strcmp(field, "VMRSAddr102") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr102;
		}
		else if (strcmp(field, "VMRSAddr103") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr103;
		}
		else if (strcmp(field, "VMRSAddr104") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr104;
		}
		else if (strcmp(field, "VMRSAddr105") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr105;
		}
		else if (strcmp(field, "VMRSAddr106") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr106;
		}
		else if (strcmp(field, "VMRSAddr107") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr107;
		}
		else if (strcmp(field, "VMRSAddr108") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr108;
		}
		else if (strcmp(field, "VMRSAddr109") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr109;
		}
		else if (strcmp(field, "VMRSAddr110") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr110;
		}
		else if (strcmp(field, "VMRSAddr111") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr111;
		}
		else if (strcmp(field, "VMRSAddr112") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr112;
		}
		else if (strcmp(field, "VMRSAddr113") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr113;
		}
		else if (strcmp(field, "VMRSAddr114") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr114;
		}
		else if (strcmp(field, "VMRSAddr115") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr115;
		}
		else if (strcmp(field, "VMRSAddr116") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr116;
		}
		else if (strcmp(field, "VMRSAddr117") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr117;
		}
		else if (strcmp(field, "VMRSAddr118") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr118;
		}
		else if (strcmp(field, "VMRSAddr119") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr119;
		}
		else if (strcmp(field, "VMRSAddr120") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr120;
		}
		else if (strcmp(field, "VMRSAddr121") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr121;
		}
		else if (strcmp(field, "VMRSAddr122") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr122;
		}
		else if (strcmp(field, "VMRSAddr123") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr123;
		}
		else if (strcmp(field, "VMRSAddr124") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr124;
		}
		else if (strcmp(field, "VMRSAddr125") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr125;
		}
		else if (strcmp(field, "VMRSAddr126") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr126;
		}
		else if (strcmp(field, "VMRSAddr127") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSAddr127;
		}
		else if (strcmp(field, "VMRSData0") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData0;
		}
		else if (strcmp(field, "VMRSData1") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData1;
		}
		else if (strcmp(field, "VMRSData2") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData2;
		}
		else if (strcmp(field, "VMRSData3") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData3;
		}
		else if (strcmp(field, "VMRSData4") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData4;
		}
		else if (strcmp(field, "VMRSData5") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData5;
		}
		else if (strcmp(field, "VMRSData6") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData6;
		}
		else if (strcmp(field, "VMRSData7") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData7;
		}
		else if (strcmp(field, "VMRSData8") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData8;
		}
		else if (strcmp(field, "VMRSData9") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData9;
		}
		else if (strcmp(field, "VMRSData10") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData10;
		}
		else if (strcmp(field, "VMRSData11") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData11;
		}
		else if (strcmp(field, "VMRSData12") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData12;
		}
		else if (strcmp(field, "VMRSData13") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData13;
		}
		else if (strcmp(field, "VMRSData14") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData14;
		}
		else if (strcmp(field, "VMRSData15") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData15;
		}
		else if (strcmp(field, "VMRSData16") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData16;
		}
		else if (strcmp(field, "VMRSData17") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData17;
		}
		else if (strcmp(field, "VMRSData18") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData18;
		}
		else if (strcmp(field, "VMRSData19") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData19;
		}
		else if (strcmp(field, "VMRSData20") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData20;
		}
		else if (strcmp(field, "VMRSData21") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData21;
		}
		else if (strcmp(field, "VMRSData22") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData22;
		}
		else if (strcmp(field, "VMRSData23") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData23;
		}
		else if (strcmp(field, "VMRSData24") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData24;
		}
		else if (strcmp(field, "VMRSData25") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData25;
		}
		else if (strcmp(field, "VMRSData26") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData26;
		}
		else if (strcmp(field, "VMRSData27") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData27;
		}
		else if (strcmp(field, "VMRSData28") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData28;
		}
		else if (strcmp(field, "VMRSData29") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData29;
		}
		else if (strcmp(field, "VMRSData30") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData30;
		}
		else if (strcmp(field, "VMRSData31") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData31;
		}
		else if (strcmp(field, "VMRSData32") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData32;
		}
		else if (strcmp(field, "VMRSData33") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData33;
		}
		else if (strcmp(field, "VMRSData34") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData34;
		}
		else if (strcmp(field, "VMRSData35") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData35;
		}
		else if (strcmp(field, "VMRSData36") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData36;
		}
		else if (strcmp(field, "VMRSData37") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData37;
		}
		else if (strcmp(field, "VMRSData38") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData38;
		}
		else if (strcmp(field, "VMRSData39") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData39;
		}
		else if (strcmp(field, "VMRSData40") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData40;
		}
		else if (strcmp(field, "VMRSData41") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData41;
		}
		else if (strcmp(field, "VMRSData42") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData42;
		}
		else if (strcmp(field, "VMRSData43") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData43;
		}
		else if (strcmp(field, "VMRSData44") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData44;
		}
		else if (strcmp(field, "VMRSData45") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData45;
		}
		else if (strcmp(field, "VMRSData46") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData46;
		}
		else if (strcmp(field, "VMRSData47") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData47;
		}
		else if (strcmp(field, "VMRSData48") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData48;
		}
		else if (strcmp(field, "VMRSData49") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData49;
		}
		else if (strcmp(field, "VMRSData50") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData50;
		}
		else if (strcmp(field, "VMRSData51") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData51;
		}
		else if (strcmp(field, "VMRSData52") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData52;
		}
		else if (strcmp(field, "VMRSData53") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData53;
		}
		else if (strcmp(field, "VMRSData54") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData54;
		}
		else if (strcmp(field, "VMRSData55") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData55;
		}
		else if (strcmp(field, "VMRSData56") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData56;
		}
		else if (strcmp(field, "VMRSData57") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData57;
		}
		else if (strcmp(field, "VMRSData58") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData58;
		}
		else if (strcmp(field, "VMRSData59") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData59;
		}
		else if (strcmp(field, "VMRSData60") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData60;
		}
		else if (strcmp(field, "VMRSData61") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData61;
		}
		else if (strcmp(field, "VMRSData62") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData62;
		}
		else if (strcmp(field, "VMRSData63") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData63;
		}
		else if (strcmp(field, "VMRSData64") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData64;
		}
		else if (strcmp(field, "VMRSData65") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData65;
		}
		else if (strcmp(field, "VMRSData66") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData66;
		}
		else if (strcmp(field, "VMRSData67") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData67;
		}
		else if (strcmp(field, "VMRSData68") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData68;
		}
		else if (strcmp(field, "VMRSData69") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData69;
		}
		else if (strcmp(field, "VMRSData70") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData70;
		}
		else if (strcmp(field, "VMRSData71") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData71;
		}
		else if (strcmp(field, "VMRSData72") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData72;
		}
		else if (strcmp(field, "VMRSData73") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData73;
		}
		else if (strcmp(field, "VMRSData74") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData74;
		}
		else if (strcmp(field, "VMRSData75") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData75;
		}
		else if (strcmp(field, "VMRSData76") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData76;
		}
		else if (strcmp(field, "VMRSData77") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData77;
		}
		else if (strcmp(field, "VMRSData78") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData78;
		}
		else if (strcmp(field, "VMRSData79") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData79;
		}
		else if (strcmp(field, "VMRSData80") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData80;
		}
		else if (strcmp(field, "VMRSData81") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData81;
		}
		else if (strcmp(field, "VMRSData82") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData82;
		}
		else if (strcmp(field, "VMRSData83") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData83;
		}
		else if (strcmp(field, "VMRSData84") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData84;
		}
		else if (strcmp(field, "VMRSData85") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData85;
		}
		else if (strcmp(field, "VMRSData86") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData86;
		}
		else if (strcmp(field, "VMRSData87") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData87;
		}
		else if (strcmp(field, "VMRSData88") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData88;
		}
		else if (strcmp(field, "VMRSData89") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData89;
		}
		else if (strcmp(field, "VMRSData90") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData90;
		}
		else if (strcmp(field, "VMRSData91") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData91;
		}
		else if (strcmp(field, "VMRSData92") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData92;
		}
		else if (strcmp(field, "VMRSData93") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData93;
		}
		else if (strcmp(field, "VMRSData94") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData94;
		}
		else if (strcmp(field, "VMRSData95") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData95;
		}
		else if (strcmp(field, "VMRSData96") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData96;
		}
		else if (strcmp(field, "VMRSData97") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData97;
		}
		else if (strcmp(field, "VMRSData98") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData98;
		}
		else if (strcmp(field, "VMRSData99") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData99;
		}
		else if (strcmp(field, "VMRSData100") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData100;
		}
		else if (strcmp(field, "VMRSData101") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData101;
		}
		else if (strcmp(field, "VMRSData102") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData102;
		}
		else if (strcmp(field, "VMRSData103") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData103;
		}
		else if (strcmp(field, "VMRSData104") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData104;
		}
		else if (strcmp(field, "VMRSData105") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData105;
		}
		else if (strcmp(field, "VMRSData106") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData106;
		}
		else if (strcmp(field, "VMRSData107") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData107;
		}
		else if (strcmp(field, "VMRSData108") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData108;
		}
		else if (strcmp(field, "VMRSData109") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData109;
		}
		else if (strcmp(field, "VMRSData110") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData110;
		}
		else if (strcmp(field, "VMRSData111") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData111;
		}
		else if (strcmp(field, "VMRSData112") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData112;
		}
		else if (strcmp(field, "VMRSData113") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData113;
		}
		else if (strcmp(field, "VMRSData114") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData114;
		}
		else if (strcmp(field, "VMRSData115") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData115;
		}
		else if (strcmp(field, "VMRSData116") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData116;
		}
		else if (strcmp(field, "VMRSData117") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData117;
		}
		else if (strcmp(field, "VMRSData118") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData118;
		}
		else if (strcmp(field, "VMRSData119") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData119;
		}
		else if (strcmp(field, "VMRSData120") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData120;
		}
		else if (strcmp(field, "VMRSData121") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData121;
		}
		else if (strcmp(field, "VMRSData122") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData122;
		}
		else if (strcmp(field, "VMRSData123") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData123;
		}
		else if (strcmp(field, "VMRSData124") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData124;
		}
		else if (strcmp(field, "VMRSData125") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData125;
		}
		else if (strcmp(field, "VMRSData126") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData126;
		}
		else if (strcmp(field, "VMRSData127") == 0) {
			return mb_LPDDR5X_1D[ps].VMRSData127;
		}
		else {
			dwc_ddrphy_phyinit_assert(0, " [%s] unknown messageBlock field name '%s', Train2D=%d\n", __func__, field, Train2D);
			return -1;
		}
	} else if (Train2D == 1) {
		/*
		 */
	} else {
		dwc_ddrphy_phyinit_assert(0, "[ %s] invalid value for Train2D=%d\n", __func__, Train2D);
		return -3;
	}

	return 0;
}

/** @} */
