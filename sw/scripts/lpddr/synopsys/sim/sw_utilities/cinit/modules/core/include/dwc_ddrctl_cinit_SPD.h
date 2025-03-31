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


#ifndef __DWC_DDRCTL_CINIT_SPD_H__
#define __DWC_DDRCTL_CINIT_SPD_H__

#include "dwc_cinit_io.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_spd_struct.h"

ddrctl_error_t dwc_ddrctl_cinit_SPD_retrieve(void);

uint64_t decode_spd_cas_latency_ddr4(uint32_t encoded_cas_latencies_supported);

uint8_t ddrctl_cinit_get_ddr5_spd_cas_latency(SPD_aux_t *spd, const uint16_t tck_avg_ps);

#endif /* __DWC_DDRCTL_CINIT_SPD_H__ */
