/** \file
 * \brief API to set internal data structures to pre-programmed user structures.
 * \addtogroup SrcFunc
 * @{
 */

#include <stdlib.h>
#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** @brief API to program user_input_basic to pre-programmed structures
 *
 * The function copies the content of the pointed data structure into the
 * global structure used by PhyInit.
 *
 * @param[in] phyctx       PhyIinit context
 *
 * @param[in] structType   integer determines the type of input structure.
 *
 *  value | PhyInit Data Structure Type
 *  ----- | ----------------------------
 *      0 | user_input_basic
 *      1 | user_input_advanced
 *      2 | user_input_sim
 *      3 | runtime_config
 *
 * @param[in] userStruct pointer to PhyInit data structure of structType.
 * @returns EXIT_SUCCESS / EXIT_FAILURE
 */
int dwc_ddrphy_phyinit_setStruct(phyinit_config_t *phyctx, const void *userStruct, int structType)
{
	user_input_basic_t *pUserInputBasic = &phyctx->userInputBasic;
	user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
	user_input_sim_t *pUserInputSim = &phyctx->userInputSim;
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
	uint8_t status = EXIT_FAILURE;

	if (userStruct == NULL) {
		dwc_ddrphy_phyinit_assert(0, " [%s] userStruct is NULL.", __func__);
	}
	if (structType < 0) {
		dwc_ddrphy_phyinit_assert(0, " [%s] structType < 0 is invalid", __func__);
	}
	if (structType > 3) {
		dwc_ddrphy_phyinit_assert(0, " [%s] structType > 3 is invalid", __func__);
	}

	switch (structType) {
	case 0:
		memcpy((void *)pUserInputBasic, userStruct, sizeof(user_input_basic_t));
		status = EXIT_SUCCESS;
		break;
	case 1:
		memcpy((void *)pUserInputAdvanced, userStruct, sizeof(user_input_advanced_t));
		status = EXIT_SUCCESS;
		break;
	case 2:
		memcpy((void *)pUserInputSim, userStruct, sizeof(user_input_sim_t));
		status = EXIT_SUCCESS;
		break;
	case 3:
		memcpy((void *)pRuntimeConfig, userStruct, sizeof(runtime_config_t));
		status = EXIT_SUCCESS;
		break;
	default:
		dwc_ddrphy_phyinit_assert(0, " [%s] structType < 0 is invalid", __func__);
		status = EXIT_FAILURE;
		break;
	}
	return status;
}

/** @} */

/** @brief Internal function used for testing
 *
 */
phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, char *pllSettings, int pubRev)
{
	static phyinit_config_t phyConfig;

	phyConfig.runtimeConfig.skip_train = skip_train;
	phyConfig.runtimeConfig.debug = debug;
	phyConfig.runtimeConfig.pubRev = pubRev;

	if (pllSettings != NULL && strlen(pllSettings) != 0) {
		if (strlen(pllSettings) < DWC_DDRPHY_PHYINIT_PLL_SETTINGS_CHARACTER_LENGTH) {
            strncpy(phyConfig.runtimeConfig.pllSettings, pllSettings,strlen(pllSettings));
            *(phyConfig.runtimeConfig.pllSettings+(strlen(pllSettings)))= '\0';
		}
		else{
			dwc_ddrphy_phyinit_assert(0, " [%s] pllSettings path Character Limit exceeded\n", __func__);
		}
        }
	dwc_ddrphy_phyinit_cmnt(" [%s] Note: the Train2d option is deprecated, option ignored\n", __func__);
	return &phyConfig;
}

/** @brief Internal function used for testing
 *
 */
void dwc_ddrphy_phyinit_configFree(phyinit_config_t *ptr)
{

}

/** @brief Internal function used for testing
 * This file provides a function that is used to get S3 restore list
 * from array RetRegList[MAX_NUM_RET_REGS] after PHY initialization 
 * complete.  This file is only to used for verification.
 */

void dwc_ddrphy_phyinit_getS3List(int S3List[MAX_NUM_RET_REGS]) 
{
  for (int regIndx = 0; regIndx < NumRegSaved; regIndx++) {
  S3List[regIndx]=RetRegList[regIndx].Address;     
  dwc_ddrphy_phyinit_cmnt("[%s] S3List[%d] = 'h%x\n", __func__, regIndx, S3List[regIndx]);   
  }
}
