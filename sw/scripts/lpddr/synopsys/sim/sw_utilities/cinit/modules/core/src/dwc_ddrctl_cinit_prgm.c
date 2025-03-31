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


/**
 *
 * @detail The purpose of the functions in this file are to take the setting passed in structures in SubsysHdlr_t
 * and apply them to each of the registers in the controller memory map.
 * After each function is called a 32-bit value is ready to be written into the controller register map.
 * No APB bus cycles are actually executed by calling this methods.
 */
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_pre_cfg.h"
#include "dwc_ddrctl_cinit_log_config.h"
#include "ddrctl_regmap.h"

/**
 * @brief function to first call cinit_pre_cfg to preform some pre
 * configuration calculations and then to call cinit_prgm_regs to
 * program all the register values.
 * @note no registers are actually programmed at this point.
 */
void dwc_cinit_setup_mmap(void)
{
    uint8_t pstate;
    uint8_t channel;

    for (pstate = 0; pstate < hdlr->num_pstates; pstate++) {
        for (channel = 0; channel < hdlr->num_dch; channel++) {
            cinit_pre_cfg(hdlr, pstate, channel);
#ifdef DDRCTL_DDR
            // loop through per channel (num_dch) and inside
            // function itself, loop for all frequencies (num_pstates)
            // do so only for the last pstate within a channel
            if (pstate == (hdlr->num_pstates-1)) {
                cinit_pre_cfg_mrr_des(hdlr, channel, hdlr->num_pstates);
            }
#endif // DDRCTL_DDR
        }
    }
    ddrctl_cinit_log_config(hdlr);

    dwc_ddrctl_cinit_prgm(hdlr);
}

/**
 * @brief iterate through all the registers setting up a 32-bit value to
 * be programmed into each writable register.
 */
void dwc_ddrctl_cinit_prgm(SubsysHdlr_t *cinit_cfg)
{
    dwc_ddrctl_cinit_prgm_REGB_DDRC();

    dwc_ddrctl_cinit_prgm_REGB_FREQ();

    ddrctl_cinit_prgm_block_arb_port(cinit_cfg);

    dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP();

    dwc_ddrctl_cinit_prgm_REGB_IME();

    ddrctl_regmap_print_regmap(DDRCTL_TRUE);
}

