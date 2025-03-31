
/** \file
 *  \brief Implements functions used to track PHY register writes
 *  \addtogroup SrcFunc
 *  @{
 */

/*
 * PhyInit Register Interface
 * --------------------------
 *
 * This file provides a group of functions that are used to track PHY register
 * writes by intercepting io_write32 function calls.  Once the registers are
 * tracked, their value can be saved at a given time spot, and restored later
 * as required.  This implementation is useful to capture any PHY register
 * programing in any function during PHY initialization.
 */

#include <stdint.h>
#include <dwc_ddrphy_phyinit.h>

extern int TrackEn;
int TrackEn = 1;          ///< Enabled tracking of registers
extern uint8_t psLoop;
uint8_t psLoop;           ///< 0: output Pstate Loop 1: inside Pstate Loop



/*! \def PIE_SRAM_ADDR_tttt_cccc
 * \brief PIE SRAM address mask.
 */
#define PIE_SRAM_ADDR_tttt_cccc  0x44000

/*! \def RET_ADDR_tttt_cccc_MASK
 * \brief Mask to filter only the upper address bits for ACSM/PIE comparison.
 */
#define RET_ADDR_tttt_cccc_MASK  0xFF000

/** \brief Function to implement a register write to the PHY
 *
 * PhyInit io write function in turn calls the customers implemnation of APB write. .
 *
 * \param adr 32-bit integer indicating address of CSR to be written
 * \param dat 16-bit integer for the value to be written to the CSR
 * \returns \c void
 */
void dwc_ddrphy_phyinit_io_write16(uint32_t adr, uint16_t dat)
{
	dwc_ddrphy_phyinit_userCustom_io_write16(adr, dat);
	dwc_ddrphy_phyinit_cmnt("phyinit_io_write: 0x%x, 0x%x\n", adr, dat);
	dwc_ddrphy_phyinit_setReg(adr, dat);
}

/** \brief Function to implement a register write to the PHY
 *
 * PhyInit io write function in turn calls the customers implemnation of APB write. .
 *
 * \param adr 32-bit integer indicating address of CSR to be written
 * \param dat 32-bit integer for the value to be written to the CSR
 * \returns \c void
 */
void dwc_ddrphy_phyinit_io_write32(uint32_t adr, uint32_t dat)
{
	//dwc_ddrphy_phyinit_userCustom_io_write32(((adr/0xFFFF)<<16) | ((adr%0xFFFF)>>1), dat);
	dwc_ddrphy_phyinit_userCustom_io_write32( adr, dat);
	dwc_ddrphy_phyinit_cmnt("phyinit_io_write: 0x%x, 0x%x\n", adr, dat);
	dwc_ddrphy_phyinit_setReg(adr, dat); // dat isn't used by this function. No impact on dat being 16-bit vs 32-bit

}

/** \brief Function to implement a MicroContMuxSel register write, preceding by 40 dficlk delay if the write data is 0
 *
 * PhyInit io write wrapper function for CSR MicroContMuxSel  
 *  - If the write data is 0, the wrapper function first calls the customer's implemnation of userCustom_wait() function that waits 40 DfiClks,
 *    then calls the the customers implemnation of APB write.
 *  - If the write data is not 0, the wrapper function calls the customer's implemnation of APB write without any delay.
 *
 * \param dat 32-bit integer for the value to be written to the MicroContMuxSel CSR
 * \returns \c void
 */
void dwc_ddrphy_phyinit_MicroContMuxSel_write32(uint32_t dat)
{
	if (dat == 0) {
		uint32_t nDfiClks = 40;
		dwc_ddrphy_phyinit_cmnt("[%s] Wait %d nDfiClks before clearing csrMicroContMuxSel;\n", __func__, nDfiClks);
		dwc_ddrphy_phyinit_userCustom_wait(nDfiClks);
	}
  // Note: S3 waiver
  //       Purposely using userCustom_io_write32(), do not want to save MicroContMuxSel to S3 list as if this
  //       CSR is progrmamed at the beginning/end of dwc_ddrphy_phyinit_restore_sequence in dwc_ddrphy_phyinit_restore_sequence.c.
	dwc_ddrphy_phyinit_userCustom_io_write32((tAPBONLY | csr_MicroContMuxSel_ADDR), dat);
	dwc_ddrphy_phyinit_cmnt("[%s] phyinit_io_write to csr MicroContMuxSel: 0x%x, 0x%x\n", __func__, (tAPBONLY | csr_MicroContMuxSel_ADDR), dat);
}


/** \brief Tags a register if tracking is enabled in the register
 * interface
 *
 * during PhyInit registers writes, keeps track of address
 * for the purpose of restoring the PHY register state during PHY
 * retention exit process.  Tracking can be turned on/off via the
 * dwc_ddrphy_phyinit_regInterface startTrack, stopTrack instructions. By
 * default tracking is always turned on.
 *
 * a register's group assignment is determined on the first time the register is written in the
 * event it's over-writen a second time in the sequence.
 *
 * \return 0: not tracked 1: tracked
 */
int dwc_ddrphy_phyinit_trackReg(uint32_t adr)
{
	//if (!TrackEn) dwc_ddrphy_phyinit_cmnt("called trackReg: 0%x, but skipped\n", adr);
	//else dwc_ddrphy_phyinit_cmnt("called trackReg: 0%x\n", adr);
	// return if tracking is disabled
	if (TrackEn==0){
		return 0;
	}


	// search register array the address,
	int regIndx = 0;

	for (regIndx = 0; regIndx < NumRegSaved; regIndx++) {
		if (RetRegList[regIndx].Address == adr) {
			return 1;
		}
	}

	//dwc_ddrphy_phyinit_cmnt("called trackReg: 1\n");
	if (TrackEn) {	// register not found, so add it.
		//printf("not found so add regIndx:%d\n", regIndx);
		if (NumRegSaved == MAX_NUM_RET_REGS) {
			dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_regInterface:%s]  Max Number of Restore Registers reached: %d. Please recompile PhyInit with MAX_NUM_RET_REG set to larger value.\n", __func__, NumRegSaved);
			return 0;
		}
		RetRegList[regIndx].Address = adr;
		NumRegSaved++;
		//dwc_ddrphy_phyinit_cmnt("called trackReg: 2\n");
		return 1;
	}
	// should never get here.
	return 0;
}

/** \brief Configures the register interface tracking API.
 *
 * ### Usage
 * Example for retention restore
 * Register tracking is enabled by calling:
 *
 *  \code
 *  dwc_ddrphy_phyinit_regInterface(startTrack,0,0);
 *  \endcode
 *
 * from this point on any call to dwc_ddrphy_phyinit_usercustom_io_write32() in
 * return will be capture by the register interface via a call to
 * dwc_ddrphy_phyinit_trackReg(). Tracking is disabled by calling:
 *
 *  \code
 *  dwc_ddrphy_phyinit_regInterface(stopTrack,0,0);
 *  \endcode
 *
 * On calling this function, register write via
 * dwc_ddrphy_phyinit_usercustom_io_write32 are no longer tracked until a
 * stratTrack call is made.  Once all the register write are complete, saveRegs
 * command can be issue to save register values into the internal data array of
 * the register interface.  Upon retention exit restoreRegs are command can be
 * used to issue register write commands to the PHY based on values stored in
 * the array.
 *  \code
 *   dwc_ddrphy_phyinit_regInterface(saveRegs,0,0);
 *   dwc_ddrphy_phyinit_regInterface(restoreRegs,0,0);
 *  \endcode
 *
 * \return 1 on success.
 *
 * @param [in ] adr : addresss
 * @param [in ] dat : data
 * @param [in ] myRegInstr : instruction. Following are valid instructions and their usage:
 *
 *
 */
int dwc_ddrphy_phyinit_regInterface(regInstr myRegInstr, uint32_t adr, uint16_t dat)
{
	if (myRegInstr == saveRegs) {
		/**
		 *  - saveRegs:
		 *    go through all the tracked registers, issue a register read and place
		 *    the result in the data structure for future recovery.
		 */
		int regIndx = 0;
		uint32_t data;

		// Local var to track number of CSRs read (filter out the ACSM/PIE SRAM restores)
		uint32_t s3CsrCnt         = 0;
		uint32_t s3AcsmSramCsrCnt = 0;
		uint32_t s3PieSramCsrCnt  = 0;

		for (regIndx = 0; regIndx < NumRegSaved; regIndx++) {
			data = dwc_ddrphy_phyinit_userCustom_io_read32(RetRegList[regIndx].Address);
			dwc_ddrphy_phyinit_cmnt(" [%s] adr: 0x%x dat: 0x%x\n", __func__, RetRegList[regIndx].Address, data);
			RetRegList[regIndx].Value = data;
			uint32_t mask = RET_ADDR_tttt_cccc_MASK;

			if (((RetRegList[regIndx].Address) & mask) == ACSM_START_CSR_ADDR) {
				s3AcsmSramCsrCnt++;
			} else if (((RetRegList[regIndx].Address) & mask) == PIE_SRAM_ADDR_tttt_cccc) {
				s3PieSramCsrCnt++;
			} else {
				s3CsrCnt++;
			}
		}

		dwc_ddrphy_phyinit_cmnt(" [%s] Total number of LP3 IO Retention (S3) CSR reads = %d (includes ACSM/PIE SRAM CSRs)\n", __func__, NumRegSaved);
		dwc_ddrphy_phyinit_cmnt(" [%s] Number of LP3 IO Retention (S3) ACSM SRAM reads = %d\n", __func__, s3AcsmSramCsrCnt);
		dwc_ddrphy_phyinit_cmnt(" [%s] Number of LP3 IO Retention (S3) PIE SRAM reads  = %d\n", __func__, s3PieSramCsrCnt);
		dwc_ddrphy_phyinit_cmnt(" [%s] Number of LP3 IO Retention (S3) PHY CSR reads   = %d (excludes ACSM/PIE SRAM CSRs)\n", __func__, s3CsrCnt);

		return 1;
	} else if (myRegInstr == restoreRegs) {
		/**
		 *  - restoreRegs:
		 *    write PHY registers based on Address, Data value pairs stores in
		 *    RetRegList
		 */
		int regIndx = 0;

		for (regIndx = 0; regIndx < NumRegSaved; regIndx++) {
			dwc_ddrphy_phyinit_userCustom_io_write32(RetRegList[regIndx].Address, RetRegList[regIndx].Value);
		}
		return 1;
	} else if (myRegInstr == startTrack) { //Enable tracking
		/**
		 *  - startTrack:
		 *    Enable Tracking for subsequent register writes.
		 */
		TrackEn = 1;
		return 1;
	} else if (myRegInstr == stopTrack)	{ // Disable tracking
		/**
		 *  - stopTrack:
		 *    Disable Tracking for subsequent register writes.
		 */
		TrackEn = 0;
		return 1;
	} else if (myRegInstr == dumpRegs) { // Dump restore state to file.
		// TBD
		return 1;
	} else if (myRegInstr == importRegs) { // import register state from file.
		// TBD
		return 1;
	} else {
		dwc_ddrphy_phyinit_assert(0, " [%s] invalid register instruction\n\n", __func__);
	}
	// future instructions.
	return 0;
}

/** \brief Writes the register address
 *
 *
 * @param[dat] reg data
 * @param[adr] register address.

 * \return 0 on success.
 */
int dwc_ddrphy_phyinit_setReg(uint32_t adr, uint16_t dat)
{
	dwc_ddrphy_phyinit_trackReg(adr);
	return 0;

	//printf("here5\n");
	//fflush(stdout);
} // End of dwc_ddrphy_phyinit_setReg()


/** \brief Helper function that returns the current Pstate being trained.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \returns integer representing PState currently being trained.
 */
extern int dwc_ddrphy_phyinit_getCurPState(phyinit_config_t *phyctx);
int dwc_ddrphy_phyinit_getCurPState(phyinit_config_t *phyctx)
{
	runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;

	return pRuntimeConfig->curPState;
}

/** @} */
