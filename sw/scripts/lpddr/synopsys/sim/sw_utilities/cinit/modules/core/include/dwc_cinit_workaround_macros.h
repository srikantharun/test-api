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

#ifndef __CINIT_WORKAROUND_MACROS__H__
#define __CINIT_WORKAROUND_MACROS__H__

#define DWC_DDRCTL_P80001562_230105_WORKAROUND

/**
 * @brief workaround macros DWC_DDRCTL_LPDDR54_OSCO_P80001562_377363
 * tOSCO needs to be increased to workaround CK stop issue during dfi_ctrlupd_req/ack
 * If this is defined, then the following error can be avoided
 * [register_fail:mpc_training_group:LPDDR5:mpc_osc_stop_to_mpc_osc_start_command_toscint_delay_check]
 */
#define DWC_DDRCTL_LPDDR54_OSCO_P80001562_377363

#endif
