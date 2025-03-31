// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


#include "dwc_ddr_sinit_vrfy_io.h"

/**
 * Functions defined on the simulation environment
 */
extern void dwc_ddrctl_cinit_sim_io_signal_tb(uint32_t sig_type);
extern void dwc_ddrctl_cinit_sim_io_block_appl(uint32_t sig_type);


/** @brief Send a signal or event to simulator
 *
 *  @param sig_type signal to be sent to simulation
 *
 */
void dwc_ddr_sinit_vrfy_io_signal_tb(uint32_t sig_type)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_sim_io_signal_tb(sig_type);

    SNPS_TRACE("Leaving");
}


/** @brief Signal to the application to stop/start traffic to the DRAM
 *
 * @param block stops traffic if true is passed, starts it if false
 */
void dwc_ddr_sinit_vrfy_io_block_appl(bool block)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_sim_io_block_appl(block);

    SNPS_TRACE("Leaving");
}
