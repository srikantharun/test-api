/** \file
 * \brief prints string to output file.
 */
#include <stdio.h>
#include <stdarg.h>
#include "dwc_ddrphy_phyinit.h"

/**  \addtogroup SrcFunc
 *  @{
 */

/** @brief Wrapper to printf
 *
 * This function is called by PhyInit to print information to output. The user
 * may have a different implementation as required by their \ref useModel.  In This
 * implementation, input string fmt is printed fort the output file handle
 * determined by \ref outFilePtr.
 *
 * @param[in] fmt Input
 *
 * @returns void
 */
void dwc_ddrphy_phyinit_print(const char *fmt, ...)
{
	// coverity[misra_c_2012_rule_17_1_violation]
	va_list argptr;
    // coverity[misra_c_2012_rule_17_1_violation]
	va_start(argptr, fmt);
	// coverity[misra_c_2012_rule_21_6_violation]
	vfprintf(outFilePtr, fmt, argptr);
	// coverity[misra_c_2012_rule_17_1_violation]
	va_end(argptr);
}

/** @} */
