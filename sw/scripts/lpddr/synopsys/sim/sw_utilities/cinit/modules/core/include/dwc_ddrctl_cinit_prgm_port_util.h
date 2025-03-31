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


#ifndef __DWC_DDRCTL_CINIT_PRGM_PORT_UTIL_H__
#define __DWC_DDRCTL_CINIT_PRGM_PORT_UTIL_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "bit_macros.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"

uint32_t dwc_ddrctl_get_port_bitmap();
uint32_t dwc_ddrctl_get_port_channel_bitmap();
uint32_t dwc_ddrctl_get_threshold_bitmap();
uint32_t dwc_ddrctl_get_ordered_bitmap();

uint32_t dwc_ddrctl_get_arb_ports_ch_bitmap();

uint32_t dwc_ddrctl_get_arb_ports_axi_raq_bitmap();
uint32_t dwc_ddrctl_get_arb_ports_axi_bitmap();

uint32_t dwc_ddrctl_get_xpi_vpr_bitmap();
uint32_t dwc_ddrctl_get_xpi_vpw_bitmap();

#endif /* __DWC_DDRCTL_CINIT_PRGM_PORT_UTIL_H__ */
