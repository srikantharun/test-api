/** \file
 *  \brief Implements the flow of PhyInit software to initialize the PHY
 *  \addtogroup SrcFunc
 *  @{
 */
#include "dwc_ddrphy_phyinit.h"


/** \brief This function implements the flow of PhyInit software to initialize the PHY.
 *
 * The execution sequence follows the overview figure provided in the PhyInit App Note.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns 0 on completion of the sequence, EXIT_FAILURE on error.
 * \callgraph
 */

int NumRegSaved;      //defined in phyinit.h file  
Reg_Addr_Val_t RetRegList[MAX_NUM_RET_REGS]; //defined in phyinit.h file

int dwc_ddrphy_phyinit_sequence(phyinit_config_t *phyctx)
{
	user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	int debug = pRuntimeConfig->debug;
	int pstate;
	// int prevPState;

	dwc_ddrphy_phyinit_cmnt(" [%s] Start of %s\n", __func__, __func__);
	// registering function inputs
	//pRuntimeConfig->curIMEM = 0xffff; // Reset state of IMEM in PhyInit
	pRuntimeConfig->curPState = 0;	// Reset state of IMEM in PhyInit

	// Initialize structures
	dwc_ddrphy_phyinit_initStruct(phyctx);

	// Enter user input
	dwc_ddrphy_phyinit_setDefault(phyctx);

	// User-editable function to override any user input
	dwc_ddrphy_phyinit_userCustom_overrideUserInput(phyctx);

	// Re-calculate Firmware Message Block input based on final user input
	dwc_ddrphy_phyinit_calcMb(phyctx);

	// check basic inputs
	dwc_ddrphy_phyinit_chkInputs(phyctx);

	// Printing values of user input
	if (debug != 0) {
		dwc_ddrphy_phyinit_print_dat(phyctx);
	}

	// (A) Bring up VDD, VDDQ, and VAA
	dwc_ddrphy_phyinit_userCustom_A_bringupPower(phyctx);

	// (B) Start Clocks and Reset the PHY
	dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy(phyctx);

	// (C) Initialize PHY Configuration
	dwc_ddrphy_phyinit_C_initPhyConfig(phyctx);

	// Customize any register write desired; This can include any CSR not covered by PhyInit or if
	// user wish to override values calculated in step C
	dwc_ddrphy_phyinit_userCustom_customPreTrain(phyctx);

	// Stop retention register tracking for training firmware related registers
	dwc_ddrphy_phyinit_regInterface(stopTrack, 0, 0);

	dwc_ddrphy_phyinit_cmnt("[%s] initCtrl = %d\n", __func__, pRuntimeConfig->initCtrl);

	// Load Training Firmware image
	uint8_t skip_imem = (pRuntimeConfig->initCtrl & 0x04u) >> 2;

	if (skip_imem==0) {
		dwc_ddrphy_phyinit_D_loadIMEM(phyctx);
	}

	// Create the PState execution order
	dwc_ddrphy_phyinit_getPsExecOrder(phyctx);

	// Train all PStates (note that pstate variable is not the actual Pstate but the index
	// into the psExecOrder list that has a calculate Pstate execution order based on userInput's
	for (pstate=0; pstate<(pUserInputBasic->NumPStates); pstate++) {
  
		// Set first/last PState flags
		pRuntimeConfig->firstTrainedPState = (pstate == 0);
		pRuntimeConfig->lastTrainedPState  = (pstate == (pUserInputBasic->NumPStates - 1));

		// Set current PState to pre-sorted array
		pRuntimeConfig->curPState = pRuntimeConfig->psExecOrder[pstate];
    
		// Program PState'able CSRs
		dwc_ddrphy_phyinit_sequencePsLoop(phyctx);
    
		// Set previous PState
		// prevPState = pRuntimeConfig->curPState;
	}

	// Start retention register tracking for training firmware related registers
	dwc_ddrphy_phyinit_regInterface(startTrack, 0, 0);

	// (I) Load PHY Init Engine Image / non-Pstate
	dwc_ddrphy_phyinit_I_loadPIEImage(phyctx);

	// Customize any CSR write desired to override values programmed by firmware or dwc_ddrphy_phyinit_I_loadPIEImage()
	// Non-Pstate only.
	dwc_ddrphy_phyinit_userCustom_customPostTrain(phyctx);

	// If retention is enabled, save CSRs
	if (pRuntimeConfig->RetEn == 1) {
		// Save value of tracked registers for retention restore sequence.
		dwc_ddrphy_phyinit_userCustom_saveRetRegs(phyctx);
	}


	// (J) Initialize the PHY to Mission Mode through DFI Initialization
	dwc_ddrphy_phyinit_userCustom_J_enterMissionMode(phyctx);

	dwc_ddrphy_phyinit_cmnt("[%s] End of %s\n", __func__, __func__);

	return 0;
}


/** \brief This function implements the PState Loop portion of initialization sequence.
 *
 * \param phyctx Data structure to hold user-defined parameters
 * \returns void
 * \callgraph
 */
void dwc_ddrphy_phyinit_sequencePsLoop(phyinit_config_t *phyctx)
{
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	uint8_t pstate = pRuntimeConfig->curPState;
	uint8_t pstateCtrl = 0x0;

	pstateCtrl = pRuntimeConfig->curPState & 0xfu;

	PMU_SMB_LPDDR5X_1D_t *mb1D = phyctx->mb_LPDDR5X_1D;

	uint8_t prog_csr = (pRuntimeConfig->initCtrl & 0x01u) >> 0;
	uint8_t skip_fw = (pRuntimeConfig->initCtrl & 0x02u) >> 1;
	//uint8_t skip_imem = (pRuntimeConfig->initCtrl & 0x04) >> 2;
	//uint8_t skip_dmem = (pRuntimeConfig->initCtrl & 0x08) >> 3;
	uint8_t devinit = (pRuntimeConfig->initCtrl & 0x20u) >> 5;

	// Start retention register tracking for pstate registers
	dwc_ddrphy_phyinit_regInterface(startTrack, 0, 0);

	// Pstatable Step C
	dwc_ddrphy_phyinit_C_initPhyConfigPsLoop(phyctx);

	// Stop retention register tracking for training firmware related registers
	dwc_ddrphy_phyinit_regInterface(stopTrack, 0, 0);

	// customPre Pstatable
	dwc_ddrphy_phyinit_userCustom_customPreTrainPsLoop(phyctx, pstate);

	if (pRuntimeConfig->firstTrainedPState == 1) {
	}
	
	if (prog_csr) {
		
		// Skip running training firmware entirely
		if(pRuntimeConfig->firstTrainedPState){
			dwc_ddrphy_phyinit_progCsrSkipTrain(phyctx);
		}

		// Skip running training firmware entirely
		dwc_ddrphy_phyinit_progCsrSkipTrainPsLoop(phyctx);

		// 2D execution should be turned off since progSkipTrain will do the programming
		pRuntimeConfig->Train2D = 0;
	}

	if (devinit) {
		// Only execute training firmware to initialize the DRAM and
		// skip all training steps.
		pRuntimeConfig->curD = 0;
		// Set sequence Ctrl to 0x1 to only do device initialization.
		mb1D[pstate].SequenceCtrl = 0x1;
	}

	if (skip_fw==0) {
		pRuntimeConfig->curD = 0;	// 1D

		// (E) Set the PHY input clocks to the desired frequency
		dwc_ddrphy_phyinit_userCustom_E_setDfiClk(phyctx, pstate);
		// Note: this routine implies other items such as DfiFreqRatio, DfiCtlClk are also set properly.
		// Because the clocks are controlled in the SOC, external to the software and PHY, this step intended to be
		// replaced by the user with the necessary SOC operations to achieve the new input frequency to the PHY.

		pstateCtrl |= (pRuntimeConfig->firstTrainedPState & 1u) << 4;
		pstateCtrl |= (pRuntimeConfig->lastTrainedPState  & 1u) << 5;

		mb1D[pstate].Pstate = pstateCtrl;
		dwc_ddrphy_phyinit_cmnt(" [%s] pstate %d pstateCtrl = 0x%x\n", __func__, pstate, mb1D[pstate].Pstate);

		// (F) Write the Message Block parameters for the training firmware
		dwc_ddrphy_phyinit_F_loadDMEM(phyctx);

		// (G) Execute the Training Firmware
		dwc_ddrphy_phyinit_G_execFW(phyctx);

		// (H) Read the Message Block results
		dwc_ddrphy_phyinit_H_readMsgBlock(phyctx, 0);

		// Now optionally perform 2D training for protocols that allow it
		if (pRuntimeConfig->Train2D == 1) {
			pRuntimeConfig->curD = 1; // 2D

			// 2D-F, cont.  Write the Message Block parameters for the training firmware
			dwc_ddrphy_phyinit_F_loadDMEM(phyctx);

			// 2D-G Execute the Training Firmware
			dwc_ddrphy_phyinit_G_execFW(phyctx);

			// 2D-H Read the Message Block results
			dwc_ddrphy_phyinit_H_readMsgBlock(phyctx, 1);
		} // 2D
	} else { // ! skipfw
		// @todo: function entry point for customer to do backdoor DRAM init.
	}

	//dwc_ddrphy_phyinit_cmnt(" debug 1\n" );
	//printf("End of fw Exec\n");

	// Start retention register tracking for training firmware related registers
	dwc_ddrphy_phyinit_regInterface(startTrack, 0, 0);

	// (I) Load PHY Init Engine Image / Pstate
	dwc_ddrphy_phyinit_I_loadPIEImagePsLoop(phyctx);

	// custom post pstate
	dwc_ddrphy_phyinit_userCustom_customPostTrainPsLoop(phyctx, pstate);


}

/** \brief This function creates the PState execution order used by dwc_ddrphy_phyinit_sequence()
 *
 * Using the userInputBasic inputs, the function will populate runtimeConfig.psExecOrder[] array
 * for the valid number of PState's (userInputBasic.NumPStates) with the proper order of execution.
 * Any unused PState's via userInputBasic.CfgPStates) will be marked as invalid (0xFF).
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns 0 on completion of the sequence, EXIT_FAILURE on error.
 * \callgraph
 */
void dwc_ddrphy_phyinit_getPsExecOrder(phyinit_config_t *phyctx) {
  // Get data structure pointers
  user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
  runtime_config_t   *pRuntimeConfig  = &phyctx->runtimeConfig;

  // Init the psExecOrder array
  for (uint16_t ps=0; ps<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; ps++) {
    // Initialize to 0xFF to mark as invalid since legal values are (0..3) or (0..14)
    pRuntimeConfig->psExecOrder[ps] = 0xFF;
  }

  dwc_ddrphy_phyinit_cmnt(" [%s] pUserInputBasic->NumPStates = %d\n", __func__, pUserInputBasic->NumPStates);
  dwc_ddrphy_phyinit_cmnt(" [%s] pUserInputBasic->CfgPStates = 0x%x\n", __func__, pUserInputBasic->CfgPStates);

  // LPDDR5X/5/4 create execution order based on userInputs
  
  // Get  vars from the runtimeConfig/userInputBasic
  uint16_t numPs   = pUserInputBasic->NumPStates;
  uint16_t cfgPs   = pUserInputBasic->CfgPStates;
  uint16_t firstPs = pUserInputBasic->FirstPState;

  // Index for psExecOrder
  uint16_t idxPsExec = 0;

  dwc_ddrphy_phyinit_cmnt(" [%s] numPs=%d\n", __func__, numPs);
  dwc_ddrphy_phyinit_cmnt(" [%s] cfgPs=0x%x\n", __func__, cfgPs);
  dwc_ddrphy_phyinit_cmnt(" [%s] firstPs=%d\n", __func__, firstPs);
  dwc_ddrphy_phyinit_cmnt(" [%s] idxPsExec=%d\n", __func__, idxPsExec);
  
  // Loop thru DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE and create the execution order
  for (uint16_t ps=0; ps<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; ps++) {

    // dwc_ddrphy_phyinit_cmnt(" [%s] ps=%d, idxPsExec=%d\n", __func__, ps, idxPsExec);

    // Conditions to skip:
    //  - If cfgPs[ps]==0
    //  - If ps == firstPState (i.e. the boot Pstate, this will be last)
    
    // Check for boot Pstate
    if ((cfgPs & (0x1u<<ps)) == 0) {
      continue;
    } else if (ps == firstPs) {
      continue;
    } else {
      pRuntimeConfig->psExecOrder[idxPsExec++] = ps;
    }
  }
  
  
  // Set the boot PState as last to execute
  pRuntimeConfig->psExecOrder[idxPsExec++] = firstPs;
  
  // idxPsExec should match the number of PState's from the userInput, else error out
  if (idxPsExec != numPs) {
    dwc_ddrphy_phyinit_assert(0, "[%s] Invalid PState Execution Order generated, idxPsExec=%d, pUserInputBasic->NumPStates=%d\n", __func__, idxPsExec, pUserInputBasic->NumPStates);
  }

  for (uint16_t i=0; i<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE; i++) {
	dwc_ddrphy_phyinit_cmnt(" [%s] pRuntimeConfig->psExecOrder[%d] = 0x%x\n", __func__, i, pRuntimeConfig->psExecOrder[i]);
  }
}


/** @} */
