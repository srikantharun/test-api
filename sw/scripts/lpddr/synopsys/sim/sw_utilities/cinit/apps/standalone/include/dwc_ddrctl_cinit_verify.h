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


#ifndef CINIT_APPS_STANDALONE_INCLUDE_DWC_DDRCTL_CINIT_VERIFY_H_
#define CINIT_APPS_STANDALONE_INCLUDE_DWC_DDRCTL_CINIT_VERIFY_H_

#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_log.h"

#define SNPS_VERIFY(address, data, file_type) \
    dwc_ddrctl_cinit_seq32_verify(address, data, file_type)


void dwc_ddrctl_cinit_seq32_verify(const uint32_t address, const uint32_t data, uint32_t file_out);

void dwc_ddrctl_cinit_struct_open(void);

void dwc_ddrctl_cinit_struct_close(void);

void dwc_ddrctl_cinit_default_open(void);

void dwc_ddrctl_cinit_default_close(void);

#endif /* CINIT_APPS_STANDALONE_INCLUDE_DWC_DDRCTL_CINIT_VERIFY_H_ */
