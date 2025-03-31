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


#ifndef CINIT_BSP_INCLUDE_CINIT_BSP_H_
#define CINIT_BSP_INCLUDE_CINIT_BSP_H_

#include "dwc_cinit_os_bsp.h"
#include "dwc_cinit_types.h"
#include "dwc_cinit_utils.h"
#include "dwc_cinit_platform.h"

void dwc_ddrctl_cinit_exit(uint32_t error_code);

void ddrctl_user_custom_get_key(uint16_t key_id, uint8_t key_size, uint32_t *key_data);

void dwc_ddrctl_cinit_assert_exit(const char *assertion, char *file, const char *func, int line);

#endif /* CINIT_BSP_INCLUDE_CINIT_BSP_H_ */
