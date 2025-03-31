/** \file
 * \brief Calculates messageBlock header based on user_input_basic and user_input_advanced.
 */
#include <stdlib.h>
#include "dwc_ddrphy_phyinit.h"

//Function Prototypes
double dwc_ddrphy_phyinit_powerOfFunc(unsigned int base, unsigned int index);

/**
 *  \addtogroup SrcFunc
 *  @{
 */

/** \brief Reads PhyInit inputs structures and sets relevant message block parameters.
 *
 * This function sets Message Block parameters based on user_input_basic and
 * user_input_advanced. Parameters are only set if not programed by
 * dwc_ddrphy_phyinit_userCustom_overrideUserInput() or
 * dwc_ddrphy_phyinit_setDefault(). user changes in these files takes precedence
 * over this function call.
 *
 * MessageBlock fields set ::
 *
 *  - DramType
 *  - Pstate
 *  - DRAMFreq
 *  - PllBypassEn
 *  - DfiFreqRatio
 *  - PhyOdtImpedance
 *  - PhyDrvImpedance
 *  - BPZNResVal
 *  - EnabledDQsChA (only applies to LPDDR4 protocol)
 *  - CsPresentChA (only applies to LPDDR4 protocol)
 *  - EnabledDQsChB (only applies to LPDDR4 protocol)
 *  - CsPresentChB (only applies to LPDDR4 protocol)
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */
void dwc_ddrphy_phyinit_calcMb(phyinit_config_t *phyctx)
{

	user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
	user_input_sim_t *pUserInputSim = &phyctx->userInputSim;
	pUserInputAdvanced = pUserInputAdvanced;	// to avoid warning in case it would not be used
	pUserInputSim = pUserInputSim;	// to avoid warning in case it would not be used
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
	int Train2D = pRuntimeConfig->Train2D;
	dwc_ddrphy_phyinit_cmnt("[%s] Start of %s()\n", __func__, __func__);

      
  for(uint32_t pstate=0;pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;pstate++) {
    if (pUserInputBasic->DfiFreqRatio[pstate] == 0x1) {
    pRuntimeConfig->DataRateMbps[pstate] = (uint32_t) 4*pUserInputBasic->Frequency[pstate];     
  } else {
    pRuntimeConfig->DataRateMbps[pstate] = (uint32_t) 8*pUserInputBasic->Frequency[pstate];    
  }
 }
  uint8_t NumAchn = pUserInputBasic->NumCh;
  pRuntimeConfig->NumAchnActive = (pUserInputBasic->NumActiveDbyteDfi1 == 0) ? 1 : NumAchn;
  pRuntimeConfig->NumDbyteActive = (pRuntimeConfig->NumAchnActive * pUserInputBasic->NumDbytesPerCh);
  pRuntimeConfig->NumDbyte = (NumAchn * pUserInputBasic->NumDbytesPerCh);

  for (uint32_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
	uint32_t cfgPState = pUserInputBasic->CfgPStates;
    if ((cfgPState & (0x1u << pstate)) == 0) {
      continue;
    }
    pRuntimeConfig->DfiFreq[pstate] = pUserInputBasic->Frequency[pstate];
  }
  for(uint32_t pstate=0;pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;pstate++) {
    pRuntimeConfig->tck_ps[pstate] = 1000000/pUserInputBasic->Frequency[pstate];
  }


	int NumCh = pUserInputBasic->NumCh;
	int NumDbyte;
	NumDbyte = pUserInputBasic->NumCh * pUserInputBasic->NumDbytesPerCh+1;

	int nad0 = pUserInputBasic->NumActiveDbyteDfi0;
	int nad1 = pUserInputBasic->NumActiveDbyteDfi1;

	// a few checks to make sure valid programing.
	if (nad0 < 0 || nad1 < 0 || (nad0 + nad1 <= 0) || (nad0 == 0 && NumCh == 1) || NumDbyte <= 0) {
		dwc_ddrphy_phyinit_assert(0, "[%s] NumActiveDbyteDfi0, NumActiveDbyteDfi0, NumByte out of range.\n", __func__);
	}

	if ((nad0 + nad1) > NumDbyte) {
		dwc_ddrphy_phyinit_assert(0, "[%s] NumActiveDbyteDfi0+NumActiveDbyteDfi1 is larger than NumDbyteDfi0, nad0=%d, nad1=%d and NumDbyte=%d\n", __func__,nad0,nad1,NumDbyte);
	}

	if (NumCh == 1 && nad1 != 0) {
		dwc_ddrphy_phyinit_assert(0, "[%s] NumCh==1 but NumActiveDbyteDfi1 != 0\n", __func__);
	}

	if (pUserInputBasic->NumRank_dfi1 != 0 && pUserInputBasic->NumRank_dfi1 != pUserInputBasic->NumRank_dfi0) {
		dwc_ddrphy_phyinit_assert(0,
								  "[%s] In a two channel system, PHY does not support different number of DQ's across ranks. NumRank_dfi0 must equal NumRank_dfi1 if NumRank_df1 !=0.\n",
								  __func__);
	}

#ifdef _BUILD_LPDDR4X
	_IF_LPDDR4(
		if (pUserInputBasic->Lp4xMode != 1){
			dwc_ddrphy_phyinit_assert(0, "[%s] When DRAM type is LPDDR4X, Lp4xMode should be set to 1.\n", __func__);
		}
	)
#endif

	uint8_t myps;
#ifdef _BUILD_DDR5
	uint8_t X16Override = 0x0;
	for (uint8_t tg=0;tg<4;tg ++) {
		X16Override  = (0x10==pUserInputBasic->DramDataWidth[tg]) ? (X16Override|((0x1<<tg)&0xf)) : (X16Override|0x0);//4bit value with X16 information
	}
#endif // _BUILD_DDR5
//
	// 1D message block defaults
	pRuntimeConfig->Train2D = 0;

	for (myps = 0; myps < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; myps++) {

		uint16_t offset = 0;	
		// Always provide valid ACSM addresses to Firmware, regardless if certain PStates are used or not
		_IF_LPDDR4(
			offset = DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP4 + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP4*2;
			mb1D[myps].FCDfi0AcsmStartPS0 = ACSM_NOP_ROW_OFFSET + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP4;
			mb1D[myps].FCDfi1AcsmStartPS0 = ACSM_NOP_ROW_OFFSET + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP4 + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP4;
			mb1D[myps].FCDfi0AcsmStartPS1 = mb1D[myps].FCDfi0AcsmStartPS0 + offset;
			mb1D[myps].FCDfi1AcsmStartPS1 = mb1D[myps].FCDfi1AcsmStartPS0 + offset;
			mb1D[myps].FCDfi0AcsmStartPS2 = mb1D[myps].FCDfi0AcsmStartPS1 + offset;
			mb1D[myps].FCDfi1AcsmStartPS2 = mb1D[myps].FCDfi1AcsmStartPS1 + offset;
			mb1D[myps].FCDfi0AcsmStartPS3 = mb1D[myps].FCDfi0AcsmStartPS2 + offset;
			mb1D[myps].FCDfi1AcsmStartPS3 = mb1D[myps].FCDfi1AcsmStartPS2 + offset;
		)
		_IF_LPDDR5(
			offset = DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP5 + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP5*2;
			mb1D[myps].FCDfi0AcsmStartPS0 = ACSM_NOP_ROW_OFFSET + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP5;
			mb1D[myps].FCDfi1AcsmStartPS0 = ACSM_NOP_ROW_OFFSET + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_COMMON_LP5 + DWC_DDRPHY_PHYINIT_NUM_PSTATE_MRS_ROWS_TRAINED_LP5;
			mb1D[myps].FCDfi0AcsmStartPS1 = mb1D[myps].FCDfi0AcsmStartPS0 + offset;
			mb1D[myps].FCDfi1AcsmStartPS1 = mb1D[myps].FCDfi1AcsmStartPS0 + offset;
			mb1D[myps].FCDfi0AcsmStartPS2 = mb1D[myps].FCDfi0AcsmStartPS1 + offset;
			mb1D[myps].FCDfi1AcsmStartPS2 = mb1D[myps].FCDfi1AcsmStartPS1 + offset;
			mb1D[myps].FCDfi0AcsmStartPS3 = mb1D[myps].FCDfi0AcsmStartPS2 + offset;
			mb1D[myps].FCDfi1AcsmStartPS3 = mb1D[myps].FCDfi1AcsmStartPS2 + offset;
		)

		// Only perform checks on PStates that are defined
		uint32_t cfgPState = pUserInputBasic->CfgPStates;
		if ((cfgPState & 0x1u << myps) == 0) {
			continue;
		}
		if (pUserInputBasic->DramDataWidth == 8 && mb1D[myps].X8Mode == 0x0) {
			dwc_ddrphy_phyinit_assert(0, "[%s] LPDDR DramDataWidth == 8 but no X8 devices programmed in mb1D[%d].X8Mode!\n", __func__, myps);
		}

		_IF_LPDDR5(
			dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "DRAMFreq", pUserInputBasic->Frequency[myps] * (pUserInputBasic->DfiFreqRatio[myps] * 2) * 2);
		)
		_IF_LPDDR4(
			dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "DRAMFreq", pUserInputBasic->Frequency[myps] * 2);
		)
		dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "PllBypassEn", pUserInputBasic->PllBypass[myps]);
		dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "DfiFreqRatio", pUserInputBasic->DfiFreqRatio[myps] == 0 ? 1 : (pUserInputBasic->DfiFreqRatio[myps] == 1 ? 2 : 4));
		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "PhyOdtImpedance", 0);
		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "PhyDrvImpedance", 0);
		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps, "BPZNResVal", 0);

		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"EnabledDQsChA",nad0 * 8);
		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"CsPresentChA",(2 == pUserInputBasic->NumRank_dfi0) ? 0x3 : pUserInputBasic->NumRank_dfi0);
		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"EnabledDQsChB",nad1 * 8);
		//dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"CsPresentChB",(2 == pUserInputBasic->NumRank_dfi1) ? 0x3 : pUserInputBasic->NumRank_dfi1);
		dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"SequenceCtrl",pUserInputAdvanced->TrainSequenceCtrl[myps]);
		if ((mb1D[myps].EnabledDQsChA == 0 && NumCh == 1) || (mb1D[myps].EnabledDQsChA == 0 && mb1D[myps].EnabledDQsChB == 0 && NumCh == 2)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] NumActiveDbyteDfi0, NumActiveDbyteDfi0, NumByte out of range.\n", __func__);
		}
		_IF_DDR5(
			(void)dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"Pstate",myps);
			(void)dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"DRAMFreq",pUserInputBasic->Frequency[myps] * 2);
			(void)dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"X16Present",(X16Override & (mb1D[myps].CsPresentChA | mb1D[myps].CsPresentChB)));
			(void)dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"EnabledDQsChA", (nad0 == 5) ? (nad0*8 -pUserInputAdvanced->Nibble_ECC*4) : (nad0*8));
			(void)dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"EnabledDQsChB", (nad1 == 5) ? (nad1*8 -pUserInputAdvanced->Nibble_ECC*4) : (nad1*8));
			// CsPresentChA/B are programmed in dwc_ddrphy_phyinit_setDefault() to allow greater user control
			//dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"CsPresentChA", 0xf >> (4-pUserInputBasic->NumRank_dfi0));
			//dwc_ddrphy_phyinit_softSetMb(phyctx, myps,"CsPresentChB", 0xf >> (4-pUserInputBasic->NumRank_dfi1));
                )
	mb1D[myps].UpperLowerByte = pUserInputAdvanced->DramByteSwap;
	} // myps
	pRuntimeConfig->Train2D = Train2D;

	_IF_DDR5(
		//##############################################################
		//
		// Calculates and replaces value for userInputSim->tCASL_add
		// when userInputSim->tCASL_override is set to 0.
		//
		// Set userInputSim->tCASL_override to 1
		// to manually set userInputSim->tCASL_add.
		//
		// Dependencies:
		//      userInputSim->tCASL_override
		//
		//##############################################################
                unsigned tg;
                for (tg=0; tg < 4; tg++) {
                	pRuntimeConfig->TG_active[tg] = 0x0; // Inidicates if certain TG is used
                	// 0 = TG is not used
                	// 1 = TG used for other DIMMs and protocol
                	if ( ( (mb1D[0].CsPresentChA & (0x1 << tg)) | (mb1D[0].CsPresentChB & (0x1 << tg)) ) > 0 )
                		pRuntimeConfig->TG_active[tg] = 0x1;
                	else
                		pRuntimeConfig->TG_active[tg] = 0x0;
                	dwc_ddrphy_phyinit_cmnt ("[%s] TG_active[%d] = %d\n", __func__, tg, pRuntimeConfig->TG_active[tg]);
                }		
		if(!pUserInputSim->tCASL_override){

			for (myps=0; myps<pUserInputBasic->NumPStates; myps++) {
				for (tg=0; tg < 4; tg++) { // foreach timing group (tg)
					pUserInputSim->tCASL_add[myps][tg] = 0;
					dwc_ddrphy_phyinit_cmnt ("[%s] userInputSim.tCASL_add[pstate=%d][tg=%d] = %d ps\n", __func__, myps, tg, pUserInputSim->tCASL_add[myps][tg]);
				}
			}
		} //tCASL_override
	)

	dwc_ddrphy_phyinit_cmnt("[%s] End of %s()\n", __func__, __func__);
}

/** \brief Calculates the result of index operations
 *
 * This function calculates the result of base number raised to the power of an index number 
 *
 * \param integer base number
 * \param integer index
 * 
 * \return double
 */
double dwc_ddrphy_phyinit_powerOfFunc(unsigned int base, unsigned int index)
{
	double result = 1;
	while (index != 0) {
		result *= base;
		--index;
	}
	return result;
}
/** @} */
