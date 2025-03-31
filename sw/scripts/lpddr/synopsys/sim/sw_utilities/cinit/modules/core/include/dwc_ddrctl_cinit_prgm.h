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


#ifndef __DWC_DDRCTL_CINIT_PRGM_H__
#define __DWC_DDRCTL_CINIT_PRGM_H__

#include "dwc_cinit_io.h"

void dwc_ddrctl_cinit_prgm(SubsysHdlr_t *cinit_cfg);

void dwc_ddrctl_cinit_prgm_ucode(SubsysHdlr_t *cinit_cfg);
void dwc_ddrctl_cinit_prgm_cfgbuf(SubsysHdlr_t *cinit_cfg);
void dwc_ddrctl_cinit_prgm_hwffcmrw(SubsysHdlr_t *cinit_cfg);

void dwc_ddrctl_cinit_prgm_REGB_FREQ(void);
void dwc_ddrctl_cinit_prgm_REGB_DDRC(void);

void ddrctl_cinit_arb_port_write(uint32_t address, uint32_t value);

void ddrctl_cinit_prgm_block_arb_port(SubsysHdlr_t *cinit_cfg);

void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP(void);
void dwc_ddrctl_cinit_prgm_REGB_IME(void);

#endif /* __DWC_DDRCTL_CINIT_PRGM_H__ */
