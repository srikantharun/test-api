/** \file
 * \brief implementation of Wait Time
 * \addtogroup CustFunc
 *  @{
 */
#include <dwc_ddrphy_phyinit.h>
/** \brief function to implement Wait Time feature
 *
 * The default behvior of dwc_ddrphy_phyinit_userCustom_wait() is to print
 * the wait time command calculated by PhyInit. User can edit this function to
 * print differently, or implement a mechanism to trigger a Wait event in
 * simulation.
 * This wait time function implements the delay in terms of DfiClks. 
 * \param  nDfiClks number of DfiClks delay to be implemented
 * \returns void
 */
extern void waitDfiClks_sv(uint32_t nDfiClks);
void dwc_ddrphy_phyinit_userCustom_wait (uint32_t nDfiClks) 
{
 waitDfiClks_sv(nDfiClks);

  char *printf_header;
  printf_header = " [dwc_ddrphy_phyinit_userCustom_wait]";
  dwc_ddrphy_phyinit_print("%s(%d);\n", __func__,nDfiClks);
	// write the Wait Time to output txt file
	dwc_ddrphy_phyinit_cmnt("Calling %s to wait %d DfiClks;\n" , printf_header, nDfiClks);
}

/** @} */

