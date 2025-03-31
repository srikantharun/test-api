/** \file
 *  \brief function to implement step B of PUB databook initialization step.
 *  \addtogroup CustFunc
 *  @{
 */

#include "dwc_ddrphy_phyinit_userCustom.h"

/** \brief The user can use this function to initiate the clocks and reset the
 * PHY.
 *
 * The default behavior of this function is to print comments relating to this
 * process. A function call of the same name will be printed in the output text
 * file. The user can choose to leave this function as is, or implement
 * mechanism within this function to trigger start clock and reset events in
 * simulation.
 *
 * See section "Clocks, Reset, Initialization" of the PUB data book for reset sequence details.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */
void dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy(phyinit_config_t *phyctx)
{
	dwc_ddrphy_phyinit_cmnt("[%s] Start of %s()\n", __func__, __func__);
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("##############################################################\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("Step (B) Start Clocks and Reset the PHY\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("See PhyInit App Note for detailed description and function usage\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("##############################################################\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_cmnt("\n");
	dwc_ddrphy_phyinit_print("%s (phyctx);\n\n", __func__);
	dwc_ddrphy_phyinit_cmnt("[%s] End of %s()\n", __func__, __func__);
}

/** @} */
