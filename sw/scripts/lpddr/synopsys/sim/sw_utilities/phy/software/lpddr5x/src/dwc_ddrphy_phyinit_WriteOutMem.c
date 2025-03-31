/** @file
 *  @brief Writes local memory content into the SRAM via APB interface.
 *  @addtogroup SrcFunc
 *  @{
 */
#include <stdio.h>
#include "dwc_ddrphy_phyinit.h"

/**
 * @brief Writes local memory content into the SRAM via APB interface.
 *
 * This function issued APB writes commands to SRAM address based on values
 * stored in a local PhyInit array that contains consolidated IMEM and DMEM
 * data.
 * @param[in] mem[]        Local memory array.
 *
 * @param[in] mem_offset   Offset index. if provided, skips to the offset index
 * from the local array and issues APB commands from mem_offset to mem_size.
 *
 * @param[in] mem_size     Size of the memroy (in mem array index)
 *
 * @param[in] sparse_write  If *dmem.incv file is passed to storeIncv (), sparse_write
 * will be set to 1 and only non zero data will be programmed.
 *
 * @returns void
 */
void dwc_ddrphy_phyinit_WriteOutMem(uint32_t mem[], int mem_offset, int mem_size, int sparse_write)
{
  int index;
  dwc_ddrphy_phyinit_cmnt(" [%s] STARTING. offset 0x%x size 0x%x, sparse_write=%d\n", __func__, mem_offset, mem_size, sparse_write);
  for (index = 0; index < mem_size; index++) {
    // dwc_ddrphy_phyinit_print("WriteOutMem: Attempting Write: Adr:0x%x Dat: 0x%x\n", index + mem_offset, mem[index]);
    if (sparse_write==0 || (sparse_write==1 && mem[index]!=0x0)) {
      dwc_ddrphy_phyinit_userCustom_io_write32(index + mem_offset, mem[index]);
    }
    // coverity[misra_c_2012_rule_21_6_violation]
    fflush(stdout);
  }

  dwc_ddrphy_phyinit_cmnt(" [%s] DONE.  Index 0x%x\n", __func__, index);
  // coverity[misra_c_2012_rule_21_6_violation]
  fflush(stdout);
}

/** @} */
