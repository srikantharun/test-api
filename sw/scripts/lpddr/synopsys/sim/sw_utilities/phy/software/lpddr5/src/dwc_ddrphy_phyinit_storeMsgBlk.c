/**
 * \file
 * \brief Store the message block into the bottom of the local DMEM array
 *
 * \addtogroup SrcFunc
 * @{
 */
#include "dwc_ddrphy_phyinit.h"

/** \brief Store the message block into the bottom of the local DMEM array
 *
 * \return void
 */
void dwc_ddrphy_phyinit_storeMsgBlk(void *msgBlkPtr, int sizeOfMsgBlk, uint32_t mem[])
{
	// Local variables
	int loop;
	uint32_t *dataArray;

	// Recast the structure pointer as a pointer to an array of 16-bit values
	dataArray = (uint32_t *) msgBlkPtr;

	// Loop over the structure 16 bits at a time and load dmem
	for (loop = 0; loop < (sizeOfMsgBlk / sizeof(uint32_t)); loop++) {
		// The data is the data in the structure at the loop offset
		mem[loop] = dataArray[loop];
	}
}

/** @} */
