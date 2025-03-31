/** \file
 * \brief implements of a print function
 *
 *  \addtogroup SrcFunc
 *  @{
 */

#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include "dwc_ddrphy_phyinit.h"


/** @brief Wrapper to printf
 *
 * This function is called by PhyInit to print comments to output txt file. The user
 * may have a different implementation as required by their \ref useModel.  In This
 * implementation for \ref useModel, the input string fmt is prepended with
 * commnt_string specified via the command line and then printed to the output
 * txt. See \ref ctrlout for more details.
 *
 * @param[in] fmt Input
 *
 * @returns void
 */
void dwc_ddrphy_phyinit_cmnt(const char *fmt, ...)
{
	// coverity[misra_c_2012_rule_17_1_violation]
	va_list argptr;
    // coverity[misra_c_2012_rule_17_1_violation]
	va_start(argptr, fmt);
	// coverity[misra_c_2012_rule_21_6_violation]
	fprintf(outFilePtr, "%s", CmntStr);
	// coverity[misra_c_2012_rule_21_6_violation]
	vfprintf(outFilePtr, fmt, argptr);
	// coverity[misra_c_2012_rule_17_1_violation]
	va_end(argptr);
}

/** @} */
