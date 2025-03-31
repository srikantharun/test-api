/** \file
 * \brief Calculates messageBlock header based on user_input_basic and user_input_advanced.
 */
#include <stdlib.h>
#include "dwc_ddrphy_phyinit.h"

/**
 *  \addtogroup SrcFunc
 *  @{
 */

/** \brief Check's users invalid programming.
 *
 * This function does some general checking on user configuration for invalid combinations of
 * settings.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */

void dwc_ddrphy_phyinit_chkInputs(phyinit_config_t *phyctx)
{
	user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
	PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

	uint16_t val = pUserInputBasic->CfgPStates;
	uint16_t count = 0;
        dwc_ddrphy_phyinit_cmnt("[%s] Start of %s\n", __func__, __func__);

	for (uint8_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
		count += ((val & 0x1u)==1) ? 1 : 0;
		val = val >> 1;
	}

	// Check NumPStates and CfgPStates values
	if (count != pUserInputBasic->NumPStates) {
		dwc_ddrphy_phyinit_assert(0, "[%s] count of 1's in CfgPState(=%d) must match NumPStates(=%d) .\n", __func__, count, pUserInputBasic->NumPStates);
	}


	// Deassert Dram Reset code should not be present when using LP5x Standard product
    if (pUserInputAdvanced->Lp5xDeassertDramReset == 1) {
		dwc_ddrphy_phyinit_assert(0, "[%s] Lp5xDeassertDramReset userInput is not currently in use for Lp5x standard product\n", __func__);
	}

	uint8_t skip_train = (pRuntimeConfig->initCtrl & 0x02u) >> 1;
	uint8_t skip_imem = (pRuntimeConfig->initCtrl & 0x04u) >> 2;
	uint8_t skip_dmem = (pRuntimeConfig->initCtrl & 0x08u) >> 3;

	if (skip_train==1 && ((skip_imem==0) || (skip_dmem==0))) {
		dwc_ddrphy_phyinit_assert(1, "[%s]  if skip_train ==1 then its optimal to set skip_imem and skip_dmem\n", __func__);
	}


	for (uint8_t pstate=0; pstate<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
		uint32_t cfgPStates = pUserInputBasic->CfgPStates;
		if ((cfgPStates & (0x1u << pstate)) == 0) {
			continue;
		}

		// For each enabled PState, check that PmuClockDiv is set to UcClk full data rate
		if (pUserInputAdvanced->PmuClockDiv[pstate]==1) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, PmuClockDiv must be 0, but PmuClockDiv[%d]=%d \n", __func__, pstate, pstate, pUserInputAdvanced->PmuClockDiv[pstate]);
		}

		// Check that userInput->RetrainMode is valid value
		if ((pUserInputAdvanced->RetrainMode[pstate] == 2) || (pUserInputAdvanced->RetrainMode[pstate] == 3)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, Illegal RetrainMode value, RetrainMode[%d]=%d \n", __func__, pstate, pstate, pUserInputAdvanced->RetrainMode[pstate]);
		}

		// Check that PPT2 is not applicable with datarate < 1600
		uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
		if ((pUserInputAdvanced->RetrainMode[pstate] == 4) && (DataRateMbps < 1600)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, PPT2 is not supported for datarate below 1600Mbps, RetrainMode[%d]=%d, datarate=%d \n", __func__, pstate, pstate, pUserInputAdvanced->RetrainMode[pstate], DataRateMbps);
		}

	}

  uint8_t DvfsQ = 0;
  uint8_t CkOdtDis_r0 = 0;
  uint8_t CsOdtDis_r0 = 0;
  uint8_t CaOdtDis_r0 = 0;
  uint8_t CkOdtDis_r1 = 0;
  uint8_t CsOdtDis_r1 = 0;
  uint8_t CaOdtDis_r1 = 0;
  uint8_t DqOdt = 0;
  uint8_t WckOdt = 0;
  uint8_t CaOdt = 0;

  for (uint8_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    DqOdt = mb1D[pstate].MR11_A0 & 0x07u;
    WckOdt = mb1D[pstate].MR18_A0 & 0x07u;
    CkOdtDis_r0 = (mb1D[pstate].MR17_A0 & 0x08u) >> 3;
    CsOdtDis_r0 = (mb1D[pstate].MR17_A0 & 0x10u) >> 4;
    CaOdtDis_r0 = (mb1D[pstate].MR17_A0 & 0x20u) >> 5;
    CkOdtDis_r1 = (mb1D[pstate].MR17_A1 & 0x08u) >> 3;
    CsOdtDis_r1 = (mb1D[pstate].MR17_A1 & 0x10u) >> 4;
    CaOdtDis_r1 = (mb1D[pstate].MR17_A1 & 0x20u) >> 5;
    DvfsQ = (mb1D[pstate].MR19_A0 & 0x0cu) >> 2;
    if (DvfsQ == 1 && pUserInputAdvanced->DisCheckDvfsqDramOdt[pstate] == 0) {
      if (DqOdt != 0) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM DQ ODT is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM DQ ODT is %d \n", __func__, pstate,DvfsQ,DqOdt);
      }
      if (WckOdt != 0) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM WCK ODT is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM WCK ODT is %d \n", __func__, pstate,DvfsQ,WckOdt);
      }
      if (CkOdtDis_r0 != 1) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM CK ODT rank0 is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM CK ODT disable field in MR17 is %d \n", __func__, pstate,DvfsQ,CkOdtDis_r0);
      }
      if (CsOdtDis_r0 != 1) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM CS ODT rank0 is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM CS ODT disable field in MR17 is %d \n", __func__, pstate,DvfsQ,CsOdtDis_r0);
      }
      if (CaOdtDis_r0 != 1) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM CA ODT rank0 is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM CA ODT disable field in MR17 is %d \n", __func__, pstate,DvfsQ,CaOdtDis_r0);
      }
      if (CkOdtDis_r1 != 1) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM CK ODT rank1 is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM CK ODT disable field in MR17 is %d \n", __func__, pstate,DvfsQ,CkOdtDis_r1);
      }
      if (CsOdtDis_r1 != 1) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM CS ODT rank1 is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM CS ODT disable field in MR17 is %d \n", __func__, pstate,DvfsQ,CsOdtDis_r1);
      }
      if (CaOdtDis_r1 != 1) {
        dwc_ddrphy_phyinit_assert(0, " [%s] DRAM CA ODT rank1 is not off when DVFSQ is enabled, Pstate %d , DVFSQ is %d, DRAM CA ODT disable field in MR17 is %d \n", __func__, pstate,DvfsQ,CaOdtDis_r1);
      }
    }
  }

  for (uint8_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
	if ( (pUserInputBasic->Frequency[pstate] < 10u) && (pUserInputBasic->DfiFreqRatio[pstate] == 0x1u) ) {
		dwc_ddrphy_phyinit_assert(0, "[%s] Frequency value is below minimum threshold of 10MHz\n", __func__);
	}
	if( (pUserInputBasic->Frequency[pstate] < 5u) && (pUserInputBasic->DfiFreqRatio[pstate] == 0x2u) ) {
		dwc_ddrphy_phyinit_assert(0, "[%s] Frequency value is below minimum threshold of 5MHz\n", __func__);
	}
  }

  for (uint8_t pstate = 0; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    CaOdt = (mb1D[pstate].MR11_A0 & 0x70u) >> 4;
    DqOdt = mb1D[pstate].MR11_A0 & 0x07u;
    if (pUserInputAdvanced->DisCheckImpTxRx[pstate] == 0) {
      if (CaOdt != 0) {
        CaOdt = 240 / CaOdt;
      }
      if (DqOdt != 0) {
        DqOdt = 240 / DqOdt;
      }
      if (pUserInputAdvanced->TxImpedanceDq[pstate] != DqOdt && DqOdt != 0) {
        dwc_ddrphy_phyinit_assert(0, " [%s] PHY Tx DQ value does not match DRAM DQ ODT value for Pstate %d , PHY Tx DQ is %d, DRAM DQ ODT is %d \n", __func__, pstate,pUserInputAdvanced->TxImpedanceDq[pstate],DqOdt);
      }
      if (pUserInputAdvanced->TxImpedanceAc[pstate] != CaOdt && CaOdt != 0) {
        dwc_ddrphy_phyinit_assert(0, " [%s] PHY Tx CA value does not match DRAM CA ODT value for Pstate %d , PHY Tx CA is %d, DRAM CA ODT is %d \n", __func__, pstate,pUserInputAdvanced->TxImpedanceAc[pstate],CaOdt);
      }
      if (pUserInputAdvanced->TxImpedanceCk[pstate] != CaOdt && CaOdt != 0) {
        dwc_ddrphy_phyinit_assert(0, " [%s] PHY Tx CK value does not match DRAM CK ODT value for Pstate %d , PHY Tx CK is %d, DRAM CK ODT is %d \n", __func__, pstate,pUserInputAdvanced->TxImpedanceAc[pstate],CaOdt);
      }
    }
  }

  uint32_t DataRateFirst = pRuntimeConfig->DataRateMbps[pUserInputBasic->FirstPState];
  uint8_t  PDFECFirst = mb1D[pUserInputBasic->FirstPState].MR41_A0 & 0x1u;
  for (uint8_t pstate = 0u; pstate < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
    uint32_t DataRateMbps = pRuntimeConfig->DataRateMbps[pstate];
    uint8_t PDFEC = mb1D[pstate].MR41_A0 & 0x1u;
    if (((uint32_t)(pUserInputBasic->CfgPStates) & (0x1u << pstate)) != 0u) {
      if ( (PDFECFirst != 0u) && (DataRateMbps > DataRateFirst) ) {
        dwc_ddrphy_phyinit_assert(0, " [%s] Per Pin DFE is allowed only for FirstPState with highest data rate. FirstPState is %d, DataRateMbps[%d]=%d is not the highest data rate. DataRateMbps[%d]=%d is higher.\n", __func__, pUserInputBasic->FirstPState,pUserInputBasic->FirstPState,DataRateFirst,pstate,DataRateMbps);
      }
    }
    if ( (PDFEC != 0u) && (pstate != pUserInputBasic->FirstPState) ) {
      dwc_ddrphy_phyinit_assert(0, " [%s] Per Pin DFE is allowed only for FirstPState with highest data rate. PDFEC[%d]=%d. PState %d is not FirstPState(PState %d). \n", __func__, pstate,PDFEC,pstate,pUserInputBasic->FirstPState);
    }
  }

  if ((pUserInputBasic->NumActiveDbyteDfi1 == 0 && pUserInputBasic->NumRank_dfi1 != 0) || (pUserInputBasic->NumActiveDbyteDfi1 != 0 && pUserInputBasic->NumRank_dfi1 == 0)){
    dwc_ddrphy_phyinit_assert(0, "[%s] Incorrect configration for NumRank_dfi1 = %d and NumActiveDbyteDfi1 = %d .", __func__, pUserInputBasic->NumRank_dfi1, pUserInputBasic->NumActiveDbyteDfi1);
  }

  if ((pUserInputAdvanced->DisZCalOnDataRate==0x0u) && (pUserInputAdvanced->PHYZCalPowerSaving!=0x0u)) {
    dwc_ddrphy_phyinit_assert(0, "[%s] When DisZCalOnDataRate is 0, PHYZCalPowerSaving must be 0, PHYZCalPowerSaving = %d .", __func__, pUserInputAdvanced->PHYZCalPowerSaving);
  }


  // Check userInputAdvanced->EnWck2DqoTracking[ps], if 1 PState enabled, all PState's must be enabled
  uint8_t uiEnWck2DqoTrackingEnabled = 0x0u;
  for (uint8_t pstate=0u; pstate<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
	  uint32_t cfgPStates = pUserInputBasic->CfgPStates;
    if ((cfgPStates& (0x1u << pstate)) == 0u) {
      continue;
    }

    // Set flag to track if any PState's have this userInput set
    if (pUserInputAdvanced->EnWck2DqoTracking[pstate] == 0x1u) {
      uiEnWck2DqoTrackingEnabled = 0x1u; 
      break;
    }
  }

  // If 1 userInput was set, check that all valid PState's have their userInput set
  if (uiEnWck2DqoTrackingEnabled == 0x1u) {
    for (uint8_t pstate=0u; pstate<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
		  uint32_t cfgPStates = pUserInputBasic->CfgPStates;
      if ((cfgPStates & (0x1u << pstate)) == 0u) {
        continue;
      }

      if (pUserInputAdvanced->EnWck2DqoTracking[pstate] == 0x0u) {
        dwc_ddrphy_phyinit_assert(0, "[%s] Pstate=%d, if userInput EnWck2DqoTracking has 1 PState enabled, all valid PStates must be enabled, pUserInputAdvanced->EnWck2DqoTracking[%d]=%d\n", __func__, pstate, pstate, pUserInputAdvanced->EnWck2DqoTracking[pstate]);
      }
    }
  }

  // Check userInputAdvanced->EnableSystemEcc, all values different from 0 are not valid.
  if (pUserInputAdvanced->EnableSystemEcc != 0u) {
    dwc_ddrphy_phyinit_assert(0, "[%s] Incorrect Value of UserInput EnableSystemEcc = %d \n", __func__, pUserInputAdvanced->EnableSystemEcc);
  }



	for (uint8_t pstate=0; pstate<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; pstate++) {
		// Check that MR11_B0 is not equal to MR11_A0 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR11_B0 != mb1D[pstate].MR11_A0)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR11 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR11_A0=%d, mb1D[%d].MR11_B0=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR11_A0, pstate, mb1D[pstate].MR11_B0);
		}
		
		// Check that MR17_B0 is not equal to MR17_A0 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR17_B0 != mb1D[pstate].MR17_A0)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR17 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR17_A0=%d, mb1D[%d].MR17_B0=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR17_A0, pstate, mb1D[pstate].MR17_B0);
		}
		
		// Check that MR17_B1 is not equal to MR17_A1 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR17_B1 != mb1D[pstate].MR17_A1)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR17 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR17_A1=%d, mb1D[%d].MR17_B1=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR17_A1, pstate, mb1D[pstate].MR17_B1);
		}
		
		// Check that MR18_B0 is not equal to MR18_A0 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR18_B0 != mb1D[pstate].MR18_A0)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR18 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR18_A0=%d, mb1D[%d].MR18_B0=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR18_A0, pstate, mb1D[pstate].MR18_B0);
		}
		
		// Check that MR19_B0 is not equal to MR19_A0 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR19_B0 != mb1D[pstate].MR19_A0)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR19 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR19_A0=%d, mb1D[%d].MR19_B0=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR19_A0, pstate, mb1D[pstate].MR19_B0);
		}
		
		// Check that MR41_B0 is not equal to MR41_A0 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR41_B0 != mb1D[pstate].MR41_A0)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR41 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR41_A0=%d, mb1D[%d].MR41_B0=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR41_A0, pstate, mb1D[pstate].MR41_B0);
		}
		
		// Check that MR58_B0 is not equal to MR58_A0 when PHY sending MRW commands for destination pstate  
		if ((pUserInputAdvanced->DisableFspOp == 0) && (mb1D[pstate].MR58_B0 != mb1D[pstate].MR58_A0)) {
			dwc_ddrphy_phyinit_assert(0, "[%s] Pstate %d, MR58 values for each channel must be the same when PHY sending MRW commands for destination pstate otherwise the value for channel B would be ignored, pUserInputAdvanced->DisableFspOp=%d, mb1D[%d].MR58_A0=%d, mb1D[%d].MR58_B0=%d\n", __func__, pstate, pUserInputAdvanced->DisableFspOp, pstate, mb1D[pstate].MR58_A0, pstate, mb1D[pstate].MR58_B0);
		}

	}

  dwc_ddrphy_phyinit_chkAllLegalValues(phyctx);

 dwc_ddrphy_phyinit_cmnt("[%s] End of %s\n", __func__, __func__);

}

/** \brief Check's users invalid programming.
 *
 * This function does some general checking on user configuration for invalid combinations of
 * settings.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */
void dwc_ddrphy_phyinit_chkAllLegalValues(phyinit_config_t *phyctx)
{
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  user_input_sim_t *pUserInputSim = &phyctx->userInputSim;

  dwc_ddrphy_phyinit_cmnt("[%s] Start of %s\n", __func__, __func__);

  int disableCheckAllUserInputValues = pUserInputAdvanced ->DisCheckAllUserInputsLegalVal;
  if(disableCheckAllUserInputValues==0){
	  // fields in the phyinit structures are generally signed integers
	  // using an unsigned int here can cause static code analysis errors
	  // when the minimum value = 0
	  int32_t currUiValueCheck = 0;
		
    //---------------------------------------------------------------------------------
    // Check values for User Input Basic
    //---------------------------------------------------------------------------------

    // Current check for pUserInputBasic->CfgPStates
    currUiValueCheck = pUserInputBasic->CfgPStates;
    if (!(currUiValueCheck >= 0x1 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CfgPStates with illegal value of %d. Legal values are between 0x1 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->DfiFreqRatio[0]
    currUiValueCheck = pUserInputBasic->DfiFreqRatio[0];
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DfiFreqRatio[0] with illegal value of %d. Legal values are: 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->DfiFreqRatio[1]
    currUiValueCheck = pUserInputBasic->DfiFreqRatio[1];
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DfiFreqRatio[1] with illegal value of %d. Legal values are: 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->DfiFreqRatio[2]
    currUiValueCheck = pUserInputBasic->DfiFreqRatio[2];
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DfiFreqRatio[2] with illegal value of %d. Legal values are: 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->DfiFreqRatio[3]
    currUiValueCheck = pUserInputBasic->DfiFreqRatio[3];
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DfiFreqRatio[3] with illegal value of %d. Legal values are: 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->DimmType
    currUiValueCheck = pUserInputBasic->DimmType;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DimmType with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->DramDataWidth
    currUiValueCheck = pUserInputBasic->DramDataWidth;
    if (!(currUiValueCheck == 8 || currUiValueCheck == 16)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DramDataWidth with illegal value of %d. Legal values are: 8, 16 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->DramType
    currUiValueCheck = pUserInputBasic->DramType;
    if (!(currUiValueCheck == 0x2 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DramType with illegal value of %d. Legal values are: 0x2, 0x4, 0x5 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->FirstPState
    currUiValueCheck = pUserInputBasic->FirstPState;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1 || currUiValueCheck == 2 || currUiValueCheck == 3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for FirstPState with illegal value of %d. Legal values are: 0, 1, 2, 3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->Frequency[0]
    currUiValueCheck = pUserInputBasic->Frequency[0];
    if (!(currUiValueCheck >= 5 && currUiValueCheck <= 1200)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Frequency[0] with illegal value of %d. Legal values are between 5 and 1200 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->Frequency[1]
    currUiValueCheck = pUserInputBasic->Frequency[1];
    if (!(currUiValueCheck >= 5 && currUiValueCheck <= 1200)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Frequency[1] with illegal value of %d. Legal values are between 5 and 1200 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->Frequency[2]
    currUiValueCheck = pUserInputBasic->Frequency[2];
    if (!(currUiValueCheck >= 5 && currUiValueCheck <= 1200)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Frequency[2] with illegal value of %d. Legal values are between 5 and 1200 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->Frequency[3]
    currUiValueCheck = pUserInputBasic->Frequency[3];
    if (!(currUiValueCheck >= 5 && currUiValueCheck <= 1200)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Frequency[3] with illegal value of %d. Legal values are between 5 and 1200 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->HardMacroVer
    currUiValueCheck = pUserInputBasic->HardMacroVer;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for HardMacroVer with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->Lp5xMode
    currUiValueCheck = pUserInputBasic->Lp5xMode;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp5xMode with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->MaxNumZQ
    currUiValueCheck = pUserInputBasic->MaxNumZQ;
    if (!(currUiValueCheck >= 1 && currUiValueCheck <= 16)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for MaxNumZQ with illegal value of %d. Legal values are between 1 and 16 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumActiveDbyteDfi0
    currUiValueCheck = pUserInputBasic->NumActiveDbyteDfi0;
    if (!(currUiValueCheck == 2 || currUiValueCheck == 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumActiveDbyteDfi0 with illegal value of %d. Legal values are: 2, 4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumActiveDbyteDfi1
    currUiValueCheck = pUserInputBasic->NumActiveDbyteDfi1;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 2 || currUiValueCheck == 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumActiveDbyteDfi1 with illegal value of %d. Legal values are: 0, 2, 4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumCh
    currUiValueCheck = pUserInputBasic->NumCh;
    if (!(currUiValueCheck == 1 || currUiValueCheck == 2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumCh with illegal value of %d. Legal values are: 1, 2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumDbytesPerCh
    currUiValueCheck = pUserInputBasic->NumDbytesPerCh;
    if (!(currUiValueCheck == 2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumDbytesPerCh with illegal value of %d. Legal values are: 2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumPStates
    currUiValueCheck = pUserInputBasic->NumPStates;
    if (!(currUiValueCheck >= 1 && currUiValueCheck <= 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumPStates with illegal value of %d. Legal values are between 1 and 4 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumRank
    currUiValueCheck = pUserInputBasic->NumRank;
    if (!(currUiValueCheck == 1 || currUiValueCheck == 2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumRank with illegal value of %d. Legal values are: 1, 2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumRank_dfi0
    currUiValueCheck = pUserInputBasic->NumRank_dfi0;
    if (!(currUiValueCheck == 1 || currUiValueCheck == 2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumRank_dfi0 with illegal value of %d. Legal values are: 1, 2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->NumRank_dfi1
    currUiValueCheck = pUserInputBasic->NumRank_dfi1;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1 || currUiValueCheck == 2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for NumRank_dfi1 with illegal value of %d. Legal values are: 0, 1, 2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->PclkPtrInitValOvr
    currUiValueCheck = pUserInputBasic->PclkPtrInitValOvr;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PclkPtrInitValOvr with illegal value of %d. Legal values are between 0 and 1 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->PclkPtrInitVal[0]
    currUiValueCheck = pUserInputBasic->PclkPtrInitVal[0];
    if (!(currUiValueCheck >= 3 && currUiValueCheck <= 10)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PclkPtrInitVal[0] with illegal value of %d. Legal values are between 3 and 10 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->PclkPtrInitVal[1]
    currUiValueCheck = pUserInputBasic->PclkPtrInitVal[1];
    if (!(currUiValueCheck >= 3 && currUiValueCheck <= 10)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PclkPtrInitVal[1] with illegal value of %d. Legal values are between 3 and 10 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->PclkPtrInitVal[2]
    currUiValueCheck = pUserInputBasic->PclkPtrInitVal[2];
    if (!(currUiValueCheck >= 3 && currUiValueCheck <= 10)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PclkPtrInitVal[2] with illegal value of %d. Legal values are between 3 and 10 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->PclkPtrInitVal[3]
    currUiValueCheck = pUserInputBasic->PclkPtrInitVal[3];
    if (!(currUiValueCheck >= 3 && currUiValueCheck <= 10)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PclkPtrInitVal[3] with illegal value of %d. Legal values are between 3 and 10 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputBasic->PllBypass[0]
    currUiValueCheck = pUserInputBasic->PllBypass[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PllBypass[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->PllBypass[1]
    currUiValueCheck = pUserInputBasic->PllBypass[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PllBypass[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->PllBypass[2]
    currUiValueCheck = pUserInputBasic->PllBypass[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PllBypass[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputBasic->PllBypass[3]
    currUiValueCheck = pUserInputBasic->PllBypass[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PllBypass[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    //---------------------------------------------------------------------------------
    // Check values for User Input Advanced
    //---------------------------------------------------------------------------------

    // Current check for pUserInputAdvanced->ACDlyScaleGating
    currUiValueCheck = pUserInputAdvanced->ACDlyScaleGating;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for ACDlyScaleGating with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AcInPipeEnOvr
    currUiValueCheck = pUserInputAdvanced->AcInPipeEnOvr;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AcInPipeEnOvr with illegal value of %d. Legal values are between 0 and 1 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AcInPipeEn[0]
    currUiValueCheck = pUserInputAdvanced->AcInPipeEn[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AcInPipeEn[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AcInPipeEn[1]
    currUiValueCheck = pUserInputAdvanced->AcInPipeEn[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AcInPipeEn[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AcInPipeEn[2]
    currUiValueCheck = pUserInputAdvanced->AcInPipeEn[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AcInPipeEn[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AcInPipeEn[3]
    currUiValueCheck = pUserInputAdvanced->AcInPipeEn[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AcInPipeEn[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AcQuarterDataRate
    currUiValueCheck = pUserInputAdvanced->AcQuarterDataRate;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AcQuarterDataRate with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AlertNPipeEnOvr
    currUiValueCheck = pUserInputAdvanced->AlertNPipeEnOvr;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AlertNPipeEnOvr with illegal value of %d. Legal values are between 0 and 1 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AlertNPipeEn[0]
    currUiValueCheck = pUserInputAdvanced->AlertNPipeEn[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AlertNPipeEn[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AlertNPipeEn[1]
    currUiValueCheck = pUserInputAdvanced->AlertNPipeEn[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AlertNPipeEn[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AlertNPipeEn[2]
    currUiValueCheck = pUserInputAdvanced->AlertNPipeEn[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AlertNPipeEn[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->AlertNPipeEn[3]
    currUiValueCheck = pUserInputAdvanced->AlertNPipeEn[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for AlertNPipeEn[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CalImpedanceCurrentAdjustment
    currUiValueCheck = pUserInputAdvanced->CalImpedanceCurrentAdjustment;
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CalImpedanceCurrentAdjustment with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CalInterval
    currUiValueCheck = pUserInputAdvanced->CalInterval;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CalInterval with illegal value of %d. Legal values are: 0x0, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CalOnce
    currUiValueCheck = pUserInputAdvanced->CalOnce;
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CalOnce with illegal value of %d. Legal values are: 0x1, 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CkDisVal[0]
    currUiValueCheck = pUserInputAdvanced->CkDisVal[0];
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CkDisVal[0] with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CkDisVal[1]
    currUiValueCheck = pUserInputAdvanced->CkDisVal[1];
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CkDisVal[1] with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CkDisVal[2]
    currUiValueCheck = pUserInputAdvanced->CkDisVal[2];
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CkDisVal[2] with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CkDisVal[3]
    currUiValueCheck = pUserInputAdvanced->CkDisVal[3];
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CkDisVal[3] with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CoreVddScalingMode[0]
    currUiValueCheck = pUserInputAdvanced->CoreVddScalingMode[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CoreVddScalingMode[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CoreVddScalingMode[1]
    currUiValueCheck = pUserInputAdvanced->CoreVddScalingMode[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CoreVddScalingMode[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CoreVddScalingMode[2]
    currUiValueCheck = pUserInputAdvanced->CoreVddScalingMode[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CoreVddScalingMode[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->CoreVddScalingMode[3]
    currUiValueCheck = pUserInputAdvanced->CoreVddScalingMode[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for CoreVddScalingMode[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DLEPKeyCode
    currUiValueCheck = pUserInputAdvanced->DLEPKeyCode;
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DLEPKeyCode with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DMEMLoadPerfEn
    currUiValueCheck = pUserInputAdvanced->DMEMLoadPerfEn;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DMEMLoadPerfEn with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DfiLoopbackEn
    currUiValueCheck = pUserInputAdvanced->DfiLoopbackEn;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DfiLoopbackEn with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DfiLpPipeClkDisable
    currUiValueCheck = pUserInputAdvanced->DfiLpPipeClkDisable;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DfiLpPipeClkDisable with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckAllUserInputsLegalVal
    currUiValueCheck = pUserInputAdvanced->DisCheckAllUserInputsLegalVal;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckAllUserInputsLegalVal with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckDvfsqDramOdt[0]
    currUiValueCheck = pUserInputAdvanced->DisCheckDvfsqDramOdt[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckDvfsqDramOdt[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckDvfsqDramOdt[1]
    currUiValueCheck = pUserInputAdvanced->DisCheckDvfsqDramOdt[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckDvfsqDramOdt[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckDvfsqDramOdt[2]
    currUiValueCheck = pUserInputAdvanced->DisCheckDvfsqDramOdt[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckDvfsqDramOdt[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckDvfsqDramOdt[3]
    currUiValueCheck = pUserInputAdvanced->DisCheckDvfsqDramOdt[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckDvfsqDramOdt[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckImpTxRx[0]
    currUiValueCheck = pUserInputAdvanced->DisCheckImpTxRx[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckImpTxRx[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckImpTxRx[1]
    currUiValueCheck = pUserInputAdvanced->DisCheckImpTxRx[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckImpTxRx[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckImpTxRx[2]
    currUiValueCheck = pUserInputAdvanced->DisCheckImpTxRx[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckImpTxRx[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisCheckImpTxRx[3]
    currUiValueCheck = pUserInputAdvanced->DisCheckImpTxRx[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisCheckImpTxRx[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisRxClkCLcdl[0]
    currUiValueCheck = pUserInputAdvanced->DisRxClkCLcdl[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisRxClkCLcdl[0] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisRxClkCLcdl[1]
    currUiValueCheck = pUserInputAdvanced->DisRxClkCLcdl[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisRxClkCLcdl[1] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisRxClkCLcdl[2]
    currUiValueCheck = pUserInputAdvanced->DisRxClkCLcdl[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisRxClkCLcdl[2] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisRxClkCLcdl[3]
    currUiValueCheck = pUserInputAdvanced->DisRxClkCLcdl[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisRxClkCLcdl[3] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisZCalOnDataRate
    currUiValueCheck = pUserInputAdvanced->DisZCalOnDataRate;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisZCalOnDataRate with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisableFspOp
    currUiValueCheck = pUserInputAdvanced->DisableFspOp;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisableFspOp with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisablePclkDca
    currUiValueCheck = pUserInputAdvanced->DisablePclkDca;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisablePclkDca with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisablePhyUpdate
    currUiValueCheck = pUserInputAdvanced->DisablePhyUpdate;
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisablePhyUpdate with illegal value of %d. Legal values are: 0x1, 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisablePmuEcc
    currUiValueCheck = pUserInputAdvanced->DisablePmuEcc;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisablePmuEcc with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DisableRetraining
    currUiValueCheck = pUserInputAdvanced->DisableRetraining;
    if (!(currUiValueCheck == 0x1 || currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DisableRetraining with illegal value of %d. Legal values are: 0x1, 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsOscRunTimeSel[0]
    currUiValueCheck = pUserInputAdvanced->DqsOscRunTimeSel[0];
    if (!(currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsOscRunTimeSel[0] with illegal value of %d. Legal values are: 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsOscRunTimeSel[1]
    currUiValueCheck = pUserInputAdvanced->DqsOscRunTimeSel[1];
    if (!(currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsOscRunTimeSel[1] with illegal value of %d. Legal values are: 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsOscRunTimeSel[2]
    currUiValueCheck = pUserInputAdvanced->DqsOscRunTimeSel[2];
    if (!(currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsOscRunTimeSel[2] with illegal value of %d. Legal values are: 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsOscRunTimeSel[3]
    currUiValueCheck = pUserInputAdvanced->DqsOscRunTimeSel[3];
    if (!(currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsOscRunTimeSel[3] with illegal value of %d. Legal values are: 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsSampNegRxEnSense[0]
    currUiValueCheck = pUserInputAdvanced->DqsSampNegRxEnSense[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsSampNegRxEnSense[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsSampNegRxEnSense[1]
    currUiValueCheck = pUserInputAdvanced->DqsSampNegRxEnSense[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsSampNegRxEnSense[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsSampNegRxEnSense[2]
    currUiValueCheck = pUserInputAdvanced->DqsSampNegRxEnSense[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsSampNegRxEnSense[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DqsSampNegRxEnSense[3]
    currUiValueCheck = pUserInputAdvanced->DqsSampNegRxEnSense[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DqsSampNegRxEnSense[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DramByteSwap
    currUiValueCheck = pUserInputAdvanced->DramByteSwap;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x3 || currUiValueCheck == 0xc || currUiValueCheck == 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DramByteSwap with illegal value of %d. Legal values are: 0x0, 0x3, 0xc, 0xf .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DramStateChangeEn
    currUiValueCheck = pUserInputAdvanced->DramStateChangeEn;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DramStateChangeEn with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DtoEnable
    currUiValueCheck = pUserInputAdvanced->DtoEnable;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DtoEnable with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxInPipeEnOvr
    currUiValueCheck = pUserInputAdvanced->DxInPipeEnOvr;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxInPipeEnOvr with illegal value of %d. Legal values are between 0 and 1 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxInPipeEn[0]
    currUiValueCheck = pUserInputAdvanced->DxInPipeEn[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxInPipeEn[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxInPipeEn[1]
    currUiValueCheck = pUserInputAdvanced->DxInPipeEn[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxInPipeEn[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxInPipeEn[2]
    currUiValueCheck = pUserInputAdvanced->DxInPipeEn[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxInPipeEn[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxInPipeEn[3]
    currUiValueCheck = pUserInputAdvanced->DxInPipeEn[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxInPipeEn[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxOutPipeEnOvr
    currUiValueCheck = pUserInputAdvanced->DxOutPipeEnOvr;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxOutPipeEnOvr with illegal value of %d. Legal values are between 0 and 1 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxOutPipeEn[0]
    currUiValueCheck = pUserInputAdvanced->DxOutPipeEn[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxOutPipeEn[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxOutPipeEn[1]
    currUiValueCheck = pUserInputAdvanced->DxOutPipeEn[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxOutPipeEn[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxOutPipeEn[2]
    currUiValueCheck = pUserInputAdvanced->DxOutPipeEn[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxOutPipeEn[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxOutPipeEn[3]
    currUiValueCheck = pUserInputAdvanced->DxOutPipeEn[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB || currUiValueCheck == 0xC || currUiValueCheck == 0xD || currUiValueCheck == 0xE || currUiValueCheck == 0xF)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxOutPipeEn[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxRdPipeEnOvr
    currUiValueCheck = pUserInputAdvanced->DxRdPipeEnOvr;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxRdPipeEnOvr with illegal value of %d. Legal values are between 0 and 1 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxRdPipeEn[0]
    currUiValueCheck = pUserInputAdvanced->DxRdPipeEn[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxRdPipeEn[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxRdPipeEn[1]
    currUiValueCheck = pUserInputAdvanced->DxRdPipeEn[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxRdPipeEn[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxRdPipeEn[2]
    currUiValueCheck = pUserInputAdvanced->DxRdPipeEn[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxRdPipeEn[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->DxRdPipeEn[3]
    currUiValueCheck = pUserInputAdvanced->DxRdPipeEn[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for DxRdPipeEn[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->EnLpRxDqPowerDown
    currUiValueCheck = pUserInputAdvanced->EnLpRxDqPowerDown;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for EnLpRxDqPowerDown with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->EnWck2DqoTracking[0]
    currUiValueCheck = pUserInputAdvanced->EnWck2DqoTracking[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for EnWck2DqoTracking[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->EnWck2DqoTracking[1]
    currUiValueCheck = pUserInputAdvanced->EnWck2DqoTracking[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for EnWck2DqoTracking[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->EnWck2DqoTracking[2]
    currUiValueCheck = pUserInputAdvanced->EnWck2DqoTracking[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for EnWck2DqoTracking[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->EnWck2DqoTracking[3]
    currUiValueCheck = pUserInputAdvanced->EnWck2DqoTracking[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for EnWck2DqoTracking[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->EnableSystemEcc
    currUiValueCheck = pUserInputAdvanced->EnableSystemEcc;
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for EnableSystemEcc with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->HalfTxCalCode
    currUiValueCheck = pUserInputAdvanced->HalfTxCalCode;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for HalfTxCalCode with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->IMEMLoadPerfEn
    currUiValueCheck = pUserInputAdvanced->IMEMLoadPerfEn;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for IMEMLoadPerfEn with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->Lp3DramState[0]
    currUiValueCheck = pUserInputAdvanced->Lp3DramState[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp3DramState[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->Lp3DramState[1]
    currUiValueCheck = pUserInputAdvanced->Lp3DramState[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp3DramState[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->Lp3DramState[2]
    currUiValueCheck = pUserInputAdvanced->Lp3DramState[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp3DramState[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->Lp3DramState[3]
    currUiValueCheck = pUserInputAdvanced->Lp3DramState[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp3DramState[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->Lp5xDeassertDramReset
    currUiValueCheck = pUserInputAdvanced->Lp5xDeassertDramReset;
    if (!(currUiValueCheck == 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp5xDeassertDramReset with illegal value of %d. Legal values are: 0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->Lp5xFwTinit3WaitTimex1000
    currUiValueCheck = pUserInputAdvanced->Lp5xFwTinit3WaitTimex1000;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for Lp5xFwTinit3WaitTimex1000 with illegal value of %d. Legal values are between 0 and 0 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCa[0]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCa[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCa[0] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCa[1]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCa[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCa[1] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCa[2]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCa[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCa[2] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCa[3]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCa[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCa[3] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCk[0]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCk[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCk[0] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCk[1]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCk[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCk[1] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCk[2]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCk[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCk[2] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceCk[3]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceCk[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceCk[3] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDq[0]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDq[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDq[0] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDq[1]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDq[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDq[1] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDq[2]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDq[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDq[2] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDq[3]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDq[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDq[3] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDqs[0]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDqs[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDqs[0] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDqs[1]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDqs[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDqs[1] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDqs[2]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDqs[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDqs[2] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceDqs[3]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceDqs[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceDqs[3] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceWCK[0]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceWCK[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceWCK[0] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceWCK[1]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceWCK[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceWCK[1] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceWCK[2]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceWCK[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceWCK[2] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->OdtImpedanceWCK[3]
    currUiValueCheck = pUserInputAdvanced->OdtImpedanceWCK[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for OdtImpedanceWCK[3] with illegal value of %d. Legal values are: 0, 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PHYZCalPowerSaving
    currUiValueCheck = pUserInputAdvanced->PHYZCalPowerSaving;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PHYZCalPowerSaving with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrMaxReqToAck[0]
    currUiValueCheck = pUserInputAdvanced->PhyMstrMaxReqToAck[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrMaxReqToAck[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrMaxReqToAck[1]
    currUiValueCheck = pUserInputAdvanced->PhyMstrMaxReqToAck[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrMaxReqToAck[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrMaxReqToAck[2]
    currUiValueCheck = pUserInputAdvanced->PhyMstrMaxReqToAck[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrMaxReqToAck[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrMaxReqToAck[3]
    currUiValueCheck = pUserInputAdvanced->PhyMstrMaxReqToAck[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrMaxReqToAck[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrTrainInterval[0]
    currUiValueCheck = pUserInputAdvanced->PhyMstrTrainInterval[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrTrainInterval[0] with illegal value of %d. Legal values are: 0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrTrainInterval[1]
    currUiValueCheck = pUserInputAdvanced->PhyMstrTrainInterval[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrTrainInterval[1] with illegal value of %d. Legal values are: 0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrTrainInterval[2]
    currUiValueCheck = pUserInputAdvanced->PhyMstrTrainInterval[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrTrainInterval[2] with illegal value of %d. Legal values are: 0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PhyMstrTrainInterval[3]
    currUiValueCheck = pUserInputAdvanced->PhyMstrTrainInterval[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3 || currUiValueCheck == 0x4 || currUiValueCheck == 0x5 || currUiValueCheck == 0x6 || currUiValueCheck == 0x7 || currUiValueCheck == 0x8 || currUiValueCheck == 0x9 || currUiValueCheck == 0xA || currUiValueCheck == 0xB)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PhyMstrTrainInterval[3] with illegal value of %d. Legal values are: 0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PmuClockDiv[0]
    currUiValueCheck = pUserInputAdvanced->PmuClockDiv[0];
    if (!(currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PmuClockDiv[0] with illegal value of %d. Legal values are: 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PmuClockDiv[1]
    currUiValueCheck = pUserInputAdvanced->PmuClockDiv[1];
    if (!(currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PmuClockDiv[1] with illegal value of %d. Legal values are: 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PmuClockDiv[2]
    currUiValueCheck = pUserInputAdvanced->PmuClockDiv[2];
    if (!(currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PmuClockDiv[2] with illegal value of %d. Legal values are: 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->PmuClockDiv[3]
    currUiValueCheck = pUserInputAdvanced->PmuClockDiv[3];
    if (!(currUiValueCheck == 0x0)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PmuClockDiv[3] with illegal value of %d. Legal values are: 0x0 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RetrainMode[0]
    currUiValueCheck = pUserInputAdvanced->RetrainMode[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RetrainMode[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RetrainMode[1]
    currUiValueCheck = pUserInputAdvanced->RetrainMode[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RetrainMode[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RetrainMode[2]
    currUiValueCheck = pUserInputAdvanced->RetrainMode[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RetrainMode[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RetrainMode[3]
    currUiValueCheck = pUserInputAdvanced->RetrainMode[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RetrainMode[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlRxReplica[0]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlRxReplica[0];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlRxReplica[0] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlRxReplica[1]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlRxReplica[1];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlRxReplica[1] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlRxReplica[2]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlRxReplica[2];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlRxReplica[2] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlRxReplica[3]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlRxReplica[3];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlRxReplica[3] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlWck[0]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlWck[0];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlWck[0] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlWck[1]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlWck[1];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlWck[1] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlWck[2]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlWck[2];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlWck[2] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxBiasCurrentControlWck[3]
    currUiValueCheck = pUserInputAdvanced->RxBiasCurrentControlWck[3];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxBiasCurrentControlWck[3] with illegal value of %d. Legal values are between 0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxClkTrackEn[0]
    currUiValueCheck = pUserInputAdvanced->RxClkTrackEn[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxClkTrackEn[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxClkTrackEn[1]
    currUiValueCheck = pUserInputAdvanced->RxClkTrackEn[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxClkTrackEn[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxClkTrackEn[2]
    currUiValueCheck = pUserInputAdvanced->RxClkTrackEn[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxClkTrackEn[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxClkTrackEn[3]
    currUiValueCheck = pUserInputAdvanced->RxClkTrackEn[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxClkTrackEn[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDFECtrlDq[0]
    currUiValueCheck = pUserInputAdvanced->RxDFECtrlDq[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x5)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDFECtrlDq[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x5 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDFECtrlDq[1]
    currUiValueCheck = pUserInputAdvanced->RxDFECtrlDq[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x5)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDFECtrlDq[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x5 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDFECtrlDq[2]
    currUiValueCheck = pUserInputAdvanced->RxDFECtrlDq[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x5)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDFECtrlDq[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x5 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDFECtrlDq[3]
    currUiValueCheck = pUserInputAdvanced->RxDFECtrlDq[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x5)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDFECtrlDq[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x5 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDqsTrackingThreshold[0]
    currUiValueCheck = pUserInputAdvanced->RxDqsTrackingThreshold[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1 || currUiValueCheck == 2 || currUiValueCheck == 3 || currUiValueCheck == 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDqsTrackingThreshold[0] with illegal value of %d. Legal values are: 0, 1, 2, 3, 4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDqsTrackingThreshold[1]
    currUiValueCheck = pUserInputAdvanced->RxDqsTrackingThreshold[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1 || currUiValueCheck == 2 || currUiValueCheck == 3 || currUiValueCheck == 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDqsTrackingThreshold[1] with illegal value of %d. Legal values are: 0, 1, 2, 3, 4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDqsTrackingThreshold[2]
    currUiValueCheck = pUserInputAdvanced->RxDqsTrackingThreshold[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1 || currUiValueCheck == 2 || currUiValueCheck == 3 || currUiValueCheck == 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDqsTrackingThreshold[2] with illegal value of %d. Legal values are: 0, 1, 2, 3, 4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxDqsTrackingThreshold[3]
    currUiValueCheck = pUserInputAdvanced->RxDqsTrackingThreshold[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1 || currUiValueCheck == 2 || currUiValueCheck == 3 || currUiValueCheck == 4)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxDqsTrackingThreshold[3] with illegal value of %d. Legal values are: 0, 1, 2, 3, 4 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->RxGainCtrl
    currUiValueCheck = pUserInputAdvanced->RxGainCtrl;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x7 || currUiValueCheck == 0x3 || currUiValueCheck == 0x5)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxGainCtrl with illegal value of %d. Legal values are: 0x0, 0x7, 0x3, 0x5 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SkipFlashCopy[0]
    currUiValueCheck = pUserInputAdvanced->SkipFlashCopy[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SkipFlashCopy[0] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SkipFlashCopy[1]
    currUiValueCheck = pUserInputAdvanced->SkipFlashCopy[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SkipFlashCopy[1] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SkipFlashCopy[2]
    currUiValueCheck = pUserInputAdvanced->SkipFlashCopy[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SkipFlashCopy[2] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SkipFlashCopy[3]
    currUiValueCheck = pUserInputAdvanced->SkipFlashCopy[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SkipFlashCopy[3] with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SkipPwrDnInRetrain
    currUiValueCheck = pUserInputAdvanced->SkipPwrDnInRetrain;
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SkipPwrDnInRetrain with illegal value of %d. Legal values are: 0x0, 0x1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SnoopWAEn[0]
    currUiValueCheck = pUserInputAdvanced->SnoopWAEn[0];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SnoopWAEn[0] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SnoopWAEn[1]
    currUiValueCheck = pUserInputAdvanced->SnoopWAEn[1];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SnoopWAEn[1] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SnoopWAEn[2]
    currUiValueCheck = pUserInputAdvanced->SnoopWAEn[2];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SnoopWAEn[2] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->SnoopWAEn[3]
    currUiValueCheck = pUserInputAdvanced->SnoopWAEn[3];
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for SnoopWAEn[3] with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TrainSequenceCtrl[0]
    currUiValueCheck = pUserInputAdvanced->TrainSequenceCtrl[0];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xffff)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TrainSequenceCtrl[0] with illegal value of %d. Legal values are between 0 and 0xffff .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TrainSequenceCtrl[1]
    currUiValueCheck = pUserInputAdvanced->TrainSequenceCtrl[1];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xffff)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TrainSequenceCtrl[1] with illegal value of %d. Legal values are between 0 and 0xffff .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TrainSequenceCtrl[2]
    currUiValueCheck = pUserInputAdvanced->TrainSequenceCtrl[2];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xffff)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TrainSequenceCtrl[2] with illegal value of %d. Legal values are between 0 and 0xffff .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TrainSequenceCtrl[3]
    currUiValueCheck = pUserInputAdvanced->TrainSequenceCtrl[3];
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 0xffff)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TrainSequenceCtrl[3] with illegal value of %d. Legal values are between 0 and 0xffff .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceAc[0]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceAc[0];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceAc[0] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceAc[1]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceAc[1];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceAc[1] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceAc[2]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceAc[2];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceAc[2] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceAc[3]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceAc[3];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceAc[3] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceCk[0]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceCk[0];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceCk[0] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceCk[1]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceCk[1];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceCk[1] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceCk[2]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceCk[2];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceCk[2] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceCk[3]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceCk[3];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceCk[3] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceCsCke
    currUiValueCheck = pUserInputAdvanced->TxImpedanceCsCke;
    if (!(currUiValueCheck == 400 || currUiValueCheck == 100 || currUiValueCheck == 66 || currUiValueCheck == 50)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceCsCke with illegal value of %d. Legal values are: 400, 100, 66, 50 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDq[0]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDq[0];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDq[0] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDq[1]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDq[1];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDq[1] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDq[2]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDq[2];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDq[2] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDq[3]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDq[3];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDq[3] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDqs[0]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDqs[0];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDqs[0] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDqs[1]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDqs[1];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDqs[1] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDqs[2]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDqs[2];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDqs[2] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceDqs[3]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceDqs[3];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceDqs[3] with illegal value of %d. Legal values are: 120, 60, 40 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceWCK[0]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceWCK[0];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceWCK[0] with illegal value of %d. Legal values are: 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceWCK[1]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceWCK[1];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceWCK[1] with illegal value of %d. Legal values are: 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceWCK[2]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceWCK[2];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceWCK[2] with illegal value of %d. Legal values are: 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxImpedanceWCK[3]
    currUiValueCheck = pUserInputAdvanced->TxImpedanceWCK[3];
    if (!(currUiValueCheck == 120 || currUiValueCheck == 60 || currUiValueCheck == 40 || currUiValueCheck == 30)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxImpedanceWCK[3] with illegal value of %d. Legal values are: 120, 60, 40, 30 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCA[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCA[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCA[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCA[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCA[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCA[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCA[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCA[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCA[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCA[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCA[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCA[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCK[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCK[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCK[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCK[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCK[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCK[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCK[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCK[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCK[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCK[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCK[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCK[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCS[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCS[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCS[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCS[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCS[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCS[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCS[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCS[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCS[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallCS[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallCS[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallCS[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallDq[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallDq[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallDq[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallDq[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallDq[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallDq[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallDq[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallDq[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallDq[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewFallDq[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewFallDq[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewFallDq[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCA[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCA[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCA[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCA[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCA[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCA[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCA[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCA[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCA[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCA[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCA[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCA[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCK[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCK[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCK[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCK[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCK[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCK[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCK[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCK[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCK[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCK[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCK[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCK[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCS[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCS[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCS[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCS[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCS[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCS[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCS[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCS[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCS[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseCS[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseCS[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseCS[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseDq[0]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseDq[0];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseDq[0] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseDq[1]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseDq[1];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseDq[1] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseDq[2]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseDq[2];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseDq[2] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->TxSlewRiseDq[3]
    currUiValueCheck = pUserInputAdvanced->TxSlewRiseDq[3];
    if (!(currUiValueCheck >= 0x0 && currUiValueCheck <= 0xf)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for TxSlewRiseDq[3] with illegal value of %d. Legal values are between 0x0 and 0xf .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->UseSnpsController
    currUiValueCheck = pUserInputAdvanced->UseSnpsController;
    if (!(currUiValueCheck == 0 || currUiValueCheck == 1)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for UseSnpsController with illegal value of %d. Legal values are: 0, 1 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->ZcalClkDiv[0]
    currUiValueCheck = pUserInputAdvanced->ZcalClkDiv[0];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for ZcalClkDiv[0] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->ZcalClkDiv[1]
    currUiValueCheck = pUserInputAdvanced->ZcalClkDiv[1];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for ZcalClkDiv[1] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->ZcalClkDiv[2]
    currUiValueCheck = pUserInputAdvanced->ZcalClkDiv[2];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for ZcalClkDiv[2] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3 .", __func__,currUiValueCheck);
    }

    // Current check for pUserInputAdvanced->ZcalClkDiv[3]
    currUiValueCheck = pUserInputAdvanced->ZcalClkDiv[3];
    if (!(currUiValueCheck == 0x0 || currUiValueCheck == 0x1 || currUiValueCheck == 0x2 || currUiValueCheck == 0x3)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for ZcalClkDiv[3] with illegal value of %d. Legal values are: 0x0, 0x1, 0x2, 0x3 .", __func__,currUiValueCheck);
    }

    //---------------------------------------------------------------------------------
    // Check values for User Input Sim
    //---------------------------------------------------------------------------------

    // Current check for pUserInputSim->LcdlNumSteps
    currUiValueCheck = pUserInputSim->LcdlNumSteps;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 511)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for LcdlNumSteps with illegal value of %d. Legal values are between 0 and 511 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->LcdlRxInsertionDelay
    currUiValueCheck = pUserInputSim->LcdlRxInsertionDelay;
    if (!(currUiValueCheck >= 39 && currUiValueCheck <= 104)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for LcdlRxInsertionDelay with illegal value of %d. Legal values are between 39 and 104 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->LcdlStepSizex10
    currUiValueCheck = pUserInputSim->LcdlStepSizex10;
    if (!(currUiValueCheck >= 14 && currUiValueCheck <= 39)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for LcdlStepSizex10 with illegal value of %d. Legal values are between 14 and 39 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->LcdlTxInsertionDelay
    currUiValueCheck = pUserInputSim->LcdlTxInsertionDelay;
    if (!(currUiValueCheck >= 51 && currUiValueCheck <= 141)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for LcdlTxInsertionDelay with illegal value of %d. Legal values are between 51 and 141 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->PHY_tDQS2DQ
    currUiValueCheck = pUserInputSim->PHY_tDQS2DQ;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 442)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for PHY_tDQS2DQ with illegal value of %d. Legal values are between 0 and 442 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->RxEnDlyOffset_Reserved
    currUiValueCheck = pUserInputSim->RxEnDlyOffset_Reserved;
    if (!(currUiValueCheck >= 100 && currUiValueCheck <= 200) && currUiValueCheck != 0){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for RxEnDlyOffset_Reserved with illegal value of %d. Legal values are between 100 and 200 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->tWCK2DQI
    currUiValueCheck = pUserInputSim->tWCK2DQI;
    if (!(currUiValueCheck >= 250 && currUiValueCheck <= 900)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for tWCK2DQI with illegal value of %d. Legal values are between 250 and 900 .", __func__, currUiValueCheck);
    }

    // Current check for pUserInputSim->tWCK2DQO
    currUiValueCheck = pUserInputSim->tWCK2DQO;
    if (!(currUiValueCheck >= 0 && currUiValueCheck <= 1900)){
      dwc_ddrphy_phyinit_assert(0, "[%s] ERROR Incorrect programming for tWCK2DQO with illegal value of %d. Legal values are between 0 and 1900 .", __func__, currUiValueCheck);
    }

	}

  dwc_ddrphy_phyinit_cmnt("[%s] End of %s\n", __func__, __func__);

}
/** @} */
