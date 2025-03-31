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


#ifndef CINIT_MODULES_VERIFICATION_INCLUDE_DWC_DDR_SINIT_VRFY_IO_H__
#define CINIT_MODULES_VERIFICATION_INCLUDE_DWC_DDR_SINIT_VRFY_IO_H__

#include "dwc_cinit_bsp.h"
#include "dwc_cinit_log.h"

void dwc_ddr_sinit_vrfy_io_signal_tb(uint32_t sig_type);

void dwc_ddr_sinit_vrfy_io_block_appl(bool block);

#endif /* CINIT_MODULES_VERIFICATION_INCLUDE_DWC_DDR_SINIT_VRFY_IO_H__ */
