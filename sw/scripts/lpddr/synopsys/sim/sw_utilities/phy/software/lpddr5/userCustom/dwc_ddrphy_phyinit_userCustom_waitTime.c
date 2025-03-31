/** \file
 * \brief implementation of Wait
 * \addtogroup CustFunc
 *  @{
 */
#include <dwc_ddrphy_phyinit.h>
/** \brief function to implement Wait feature
 *
 * The default behvior of dwc_ddrphy_phyinit_userCustom_waitTime() is to print
 * the wait time command calculated by PhyInit. User can edit this function to
 * print differently, or implement a mechanism to trigger a Wait time event in
 * simulation.
 * This wait function implements the delay in wall clock (time delay).
 * \param  waitTimeNs number indicating delay in wall clock time in terms of nanoseconds
 * \returns void
 */

// coverity[misra_c_2012_rule_5_1_violation]
void dwc_ddrphy_phyinit_userCustom_waitTime(uint32_t waitTimeNs)
{
  char *printf_header;
  printf_header = " [dwc_ddrphy_phyinit_userCustom_waitTime]";
  dwc_ddrphy_phyinit_print("%s(%d);\n", __func__,waitTimeNs);
	// write the Wait Time to output txt file
	dwc_ddrphy_phyinit_cmnt("Calling %s to wait %dns waitTime;\n" , printf_header, waitTimeNs);
}

/** @} */
