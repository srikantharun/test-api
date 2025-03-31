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


#ifndef __CORE_INCLUDE_CINIT_PORT_UTIL_H__
#define __CORE_INCLUDE_CINIT_PORT_UTIL_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_defines.h"
#include "cinit_status.h"

ddrctl_error_t ddrctl_cinit_wait_ports_idle(uint32_t timeout);

ddrctl_error_t ddrctl_cinit_ctrl_ports(ddrctl_status_t status, uint32_t timeout);

ddrctl_error_t ddrctl_cinit_scrubber_enable(ddrctl_channel_t channel, ddrctl_status_t status);

uint8_t ddrctl_sw_cinit_get_global_maint_calibr(uint8_t ch);

ddrctl_error_t ddrctl_sw_cinit_global_maint_calibr(uint8_t ch, uint8_t value, uint32_t timeout);

uint32_t ddrctl_sw_cinit_get_rank_maint_calibr(uint8_t ch);

ddrctl_error_t ddrctl_sw_cinit_rank_maint_calibr(uint8_t ch, uint8_t value, uint32_t timeout);

#endif /* __CORE_INCLUDE_CINIT_CTL_PORT_UTIL_H__ */
