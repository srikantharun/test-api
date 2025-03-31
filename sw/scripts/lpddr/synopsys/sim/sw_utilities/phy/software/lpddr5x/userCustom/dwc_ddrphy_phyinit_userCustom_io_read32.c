
/** \file
 * \brief implementation of APB read
 * \addtogroup CustFunc
 *  @{
 */

#include <dwc_ddrphy_phyinit.h>

/** \brief function to perform a APB register read on the PHY
 *
 * This is user-editable function.  User can edit this function according to
 * their needs.
 *
 * The user must provide an implementation for reading registers from the PHY
 * in this function.  PhyInit calls this function during PHY initialization to
 * read the register content of the PHY for the purpose of restoring the PHY
 * state during retention exit.
 *
 * Implementation of this function is only necessary if PhyInit retention
 * restore sequence feature is used.
 *
 * For the purpose of generating the output txt file, the below implementation
 * prints a "dwc_ddrphy_apb_rd()" commands to the output for reference. The
 * output text is commented out and 0 is always returned.
 *
 *  \param adr address of register to read
 *  \returns register value
 */

// coverity[misra_c_2012_rule_5_1_violation]
extern void io_read32_sv(uint32_t addr, uint32_t* data);
uint32_t dwc_ddrphy_phyinit_userCustom_io_read32(uint32_t adr)
{
	uint32_t dat;
uint32_t read_data;
io_read32_sv(adr, &dat);
read_data=dat;
return read_data;
dwc_ddrphy_phyinit_print("// %s", ApbStr);
	dwc_ddrphy_phyinit_print("dwc_ddrphy_apb_rd(32'h%x);\n", adr);

	// user must provide an implementation for returning register value
	return 0;
}

/** @} */

