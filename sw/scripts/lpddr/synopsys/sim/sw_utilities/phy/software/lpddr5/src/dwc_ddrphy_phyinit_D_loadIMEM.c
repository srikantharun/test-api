/** \file
 *  \brief Implements Step D of initialization sequence
 *  \addtogroup SrcFunc
 *  @{
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** \brief This function loads the training firmware IMEM image into the SRAM.
 *
 *  This function reads the incv files form the firmware package to generate a
 *  set of apb writes to load IMEM image into the SRAM. The exact steps in this
 *  function are as follows:
 *
 *  -# Ensure DRAM is in reset.
 *  -# Load the microcontroller memory with the provided training firmware
 *  -# Initialize the firmware mailbox structures to be able to communicate with
 *  the firmware (see "Mailbox facility for firmware" in the "DesignWare Cores
 *  DDR PHY Training Application Note".
 *
 *  Only loads IMEM image when currently not loaded in SRAM.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */
void dwc_ddrphy_phyinit_D_loadIMEM(phyinit_config_t *phyctx)
{
  user_input_advanced_t *pUserInputAdvanced = &phyctx->userInputAdvanced;
  runtime_config_t *pRuntimeConfig = &phyctx->runtimeConfig;
  uint8_t pstate = pRuntimeConfig->curPState;

  dwc_ddrphy_phyinit_cmnt(" [%s] Start of %s\n", __func__, __func__);

  uint32_t last_address = 0;
  static uint32_t mem[IMEM_SIZE/sizeof(uint32_t)];
  return_offset_lastaddr_t return_type = return_lastaddr;

  /*
   * - Disable HckEn in order to use CCMBypass
   *   - Dependencies:
   *     - user_input_advanced.PmuClockDiv
   *     - user_input_advanced.IMEMLoadPerfEn
   */
  uint16_t pmuClkEnables;

  if(pUserInputAdvanced->IMEMLoadPerfEn){
    pmuClkEnables = 0x0u<<csr_HclkEn_LSB | 0x1u<<csr_UcclkEn_LSB;
  } else {
    pmuClkEnables = csr_HclkEn_MASK | csr_UcclkEn_MASK;
  }
  if (pUserInputAdvanced->PmuClockDiv[pstate] == 0) {
    pmuClkEnables |= csr_UcclkFull_MASK;
  }
  dwc_ddrphy_phyinit_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);

  // initialize the dmem structure
  memset(mem, 0, sizeof(mem));

  // Read the IMEM INCV file into the array
  last_address = dwc_ddrphy_phyinit_storeIncvFile(IMEM_INCV_FILENAME, mem, return_type);

  if (last_address == 0) {
    dwc_ddrphy_phyinit_cmnt(" [%s] Skipping loading of IMEM, INCV offset is %d\n", __func__, last_address);
  } else {
    // Write local imem array (set performance argument to 0 so all entries of .incv are written)
    dwc_ddrphy_phyinit_WriteOutMem(mem, IMEM_ST_ADDR, (last_address-IMEM_ST_ADDR+1), 0);
  }

  dwc_ddrphy_phyinit_cmnt(" [%s] WriteImem: COMPLETED\n", __func__);
  // coverity[misra_c_2012_rule_21_6_violation]

  fflush(stdout);

  // Disabling HckEn after CCMBypass to load IMEM
  if (pUserInputAdvanced->IMEMLoadPerfEn) {
    pmuClkEnables |= 0x1u<<csr_HclkEn_LSB;
    dwc_ddrphy_phyinit_io_write32((tDRTUB | csr_UcclkHclkEnables_ADDR), pmuClkEnables);
  }

  dwc_ddrphy_phyinit_cmnt(" [%s] End of %s\n", __func__, __func__);
}

/** @} */
