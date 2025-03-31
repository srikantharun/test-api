/** \file
 *  \brief user customization before training
 *  \addtogroup CustFunc
 *  @{
 */
#include <stdio.h>
#include <stdlib.h>
#include "dwc_ddrphy_phyinit.h"

/** @brief This function is called before training firmware is executed outside the PState Loop.
 *
 * This function is executed before firmware execution loop.
 * Register override in this function will persist during training firmware execution and will have
 * an effect on training results.
 * Thus this function must be used only for the following:
 *
 *  - Override PHY register values written by
 *  dwc_ddrphy_phyinit_C_initPhyConfig.  An example use case is when this
 *  function does not perform the exact programing desired by the user.
 *  - Write custom PHY registers that need to take effect before training
 *  firmware execution that are not that are not replicated per Pstate.
 *  - Program technology specific registers described in PHY Databook that are not replicated per
 *  PState.
 *
 * User shall use dwc_ddrphy_phyinit_io_write32 to write PHY
 * registers in order for the register to be tracked by PhyInit for
 * retention restore.
 *
 * \note This functions should only contain register programming to non-PState registers. Custom
 * register programming for PStateble registers should be included in dwc_ddrphy_phyinit_userCustom_customPreTrainPsLoop()
 *
 * \warning **IMPORTANT** In this function, user shall not override any values in
 * user_input_basic, user_input_advanced or messageBlock data structures. These
 * changes should be done in dwc_ddrphy_phyinit_userCustom_overrideUserInput().
 * Changing these structures affects steps C, I and other helper functions. At
 * this point of execution flow step C has finished and changes will only be
 * seen by Step I. This will cause unexpected and untested behavior of PhyInit.
 *
 * To override settings in the message block, users can use any of two methods:
 * -# calling dwc_ddrphy_phyinit_setMb(char *field, int value) function
 * -# assign values to the fields in the message block data structure directly
 *
 *
 * \ref examples/simple/dwc_ddrphy_phyinit_userCustom_customPreTrain.c example of this function
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * @return void
 * 
 */

// coverity[misra_c_2012_rule_5_1_violation]
void dwc_ddrphy_phyinit_userCustom_customPreTrain(phyinit_config_t *phyctx)
{
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("-----------------------------------------------------\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt(" dwc_ddrphy_phyihunit_userCustom_customPreTrain is a user-editable function.\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt(" See PhyInit App Note for detailed description and function usage\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("-----------------------------------------------------\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_print("%s (phyctx);\n\n", __func__);
	dwc_ddrphy_phyinit_cmnt("[%s] Start of %s()\n", __func__, __func__);
	dwc_ddrphy_phyinit_cmnt("[%s] End of %s()\n", __func__, __func__);
}

/** @brief This function is called before training firmware is executed in the PState Loop.
 *
 * This function must be used when the desired register is replicated per PState.
 * This function is executed before firmware execution loop.
 * Register override in this function will persist during training firmware execution and will have
 * an effect on training results.
 * Thus this function must be used only for the following:
 *
 *  - Override PHY register values written by
 *  dwc_ddrphy_phyinit_C_initPhyConfigPsLoop.  An example use case is when this
 *  function does not perform the exact programing desired by the user.
 *  - Write custom PHY registers that need to take effect before training
 *  firmware execution that are not that are not replicated per Pstate.
 *  - Program technology specific registers described in PHY Databook that are not replicated per
 *  Pstate.
 *
 * User must use dwc_ddrphy_phyinit_io_write32 to write PHY
 * registers in order for the register to be tracked by PhyInit for
 * retention restore.
 *
 * \warning **IMPORTANT** In this function, user shall not override any values in
 * user_input_basic, user_input_advanced or messageBlock data structures. These
 * changes should be done in dwc_ddrphy_phyinit_userCustom_overrideUserInput().
 * Changing these structures at this points affects previous steps and may result in unknown PHY
 * behavior. At this point of execution flow step C has finished and changes will only be
 * seen by Step I. This will cause unexpected and untested behavior of PhyInit.
 *
 * To override settings in the message block, users can use any of two methods:
 * -# calling dwc_ddrphy_phyinit_setMb(char *field, int value) function
 * -# assign values to the fields in the message block data structure directly
 *
 * \ref examples/simple/dwc_ddrphy_phyinit_userCustom_customPreTrain.c example of this function
 * @param phyctx in Data structure to hold user-defined parameters
 * @param pstate in Current PState.
 *
 * @return void
 *
 */

// coverity[misra_c_2012_rule_5_1_violation]
void dwc_ddrphy_phyinit_userCustom_customPreTrainPsLoop(phyinit_config_t *phyctx, int pstate)
{
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("-----------------------------------------------------\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt(" dwc_ddrphy_phyihunit_userCustom_customPreTrainPsLoop is a user-editable function.\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt(" See PhyInit App Note for detailed description and function usage\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("-----------------------------------------------------\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("[%s] Start of %s(), PState=%d\n", __func__, __func__, pstate);

	/**
	   The values must be written to PHY FSP-0 and PhyInit register interface will will
	 * store the results additionally in the PSTATE SRAM.
	 *
	 * See Examples code provided in PhyInit for reference implementation.
	 */
	//user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	//uint32_t paddr;
	//paddr = pstate;

	//if (pstate == 0) {
	//	=== Example to override SequenceCtrl in 1D message block for each p-state
	//	=== using dwc_ddrphy_phyinit_setMb(int ps, char *field, int value, int Train2D)
	//	===
	//	dwc_ddrphy_phyinit_setMb(0, "SequenceCtrl", 0x031f, 0); // p-state 0, 1D
	//
	//	=== Example to override SequenceCtrl in 2D message block for p-state 0
	//	=== using dwc_ddrphy_phyinit_setMb(int ps, char *field, int value, int Train2D)
	//	===
	//	dwc_ddrphy_phyinit_setMb(0, "SequenceCtrl", 0x0061, 1); // p-state 0, 2D

	//	=== Example to override SequenceCtrl in 1D message block for each p-state
	//	=== by assigning the data structure sub-fields directly
	//	===
	//	mb_DDR4U_1D[0].SequenceCtrl = 0x031f; // p-state 0, 1D
	//
	//	=== Example to override SequenceCtrl in 2D message block for p-state 0
	//	=== by assigning the data structure sub-fields directly
	//	===
	//	mb_DDR4U_2D[0].SequenceCtrl = 0x0061; // p-state 0, 2D

	//	===  Example to override value in CSR PclkPtrInitVal for p-0
	//	=== paddr, tMASTER, csr_PclkPtrInitVal_ADDR make up the full address of the CSR
	//	=== They are defined in dwc_ddrphy_csr_ALL_cdefines.h included in Phyinit source folder
	//	===  - tMASTER :: MASTER block-type
	//	===  - csr_PclkPtrInitVal_ADDR :: register address
	//	===
	//	dwc_ddrphy_phyinit_io_write32((paddr | tMASTER | csr_PclkPtrInitVal_ADDR), 0x3);
	//} else if (pstate == 1) {
	//	=== A different PclkPtrInitVal setting for PS1
	//	dwc_ddrphy_phyinit_io_write32((paddr | tMASTER | csr_PclkPtrInitVal_ADDR), 0x2);
	//} else if (pstate == 2) {
	//	=== A different PclkPtrInitVal setting for PS2
	//	dwc_ddrphy_phyinit_io_write32((paddr | tMASTER | csr_PclkPtrInitVal_ADDR), 0x3);
	//} else { // all other PStates
	//	=== A different PclkPtrInitVal setting for PS1
	//	dwc_ddrphy_phyinit_io_write32((paddr | tMASTER | csr_PclkPtrInitVal_ADDR), 0x3);
	//}

	// === Example to override SequenceCtrl in 1D message block for each p-state
	// === using dwc_ddrphy_phyinit_setMb(int ps, char *field, int value, int Train2D)
	//dwc_ddrphy_phyinit_setMb(0, "SequenceCtrl", 0x031f, 0); // p-state 0, 1D
	//dwc_ddrphy_phyinit_setMb(1, "SequenceCtrl", 0x031f, 0); // p-state 1, 1D

	// === Example to override SequenceCtrl in 2D message block for p-state 0
	// === using dwc_ddrphy_phyinit_setMb(int ps, char *field, int value, int Train2D)
	//dwc_ddrphy_phyinit_setMb(0, "SequenceCtrl", 0x0061, 1); // p-state 0, 2D

	// === Example to override SequenceCtrl in 1D message block for each p-state
	// === by assigning the data structure sub-fields directly
	//mb_DDR4U_1D[0].SequenceCtrl = 0x031f; // p-state 0, 1D
	//mb_DDR4U_1D[1].SequenceCtrl = 0x031f; // p-state 1, 1D

	// === Example to override SequenceCtrl in 2D message block for p-state 0
	// === by assigning the data structure sub-fields directly
	//mb_DDR4U_2D[0].SequenceCtrl = 0x0061; // p-state 0, 2D

	dwc_ddrphy_phyinit_cmnt("[%s] End of %s(), PState=%d\n", __func__, __func__, pstate);
}

/** @} */
