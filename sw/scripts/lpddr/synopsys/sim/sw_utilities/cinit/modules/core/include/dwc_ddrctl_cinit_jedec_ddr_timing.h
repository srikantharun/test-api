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


#ifndef __DWC_DDRCTL_CINIT_JEDEC_DDR_TIMING_H__
#define __DWC_DDRCTL_CINIT_JEDEC_DDR_TIMING_H__

#include "dwc_ddrctl_cinit.h"


void dwc_cinit_get_jedec_clk_speed(SubsysHdlr_t* cfg);

ddrctl_error_t dwc_cinit_ddr_set_timing(void);


uint32_t dwc_ddrctl_cinit_get_stagger_ref_timing_max(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                                     uint32_t per_bank_refresh, uint32_t fgr_mode, uint32_t tck_ps,
                                                     uint32_t ddr5_trefi_ps, uint32_t ddr5_trfc1_ps,
                                                     uint32_t ddr5_trfc2_ps, uint32_t scaled_trefi_en,
                                                     uint32_t ddr4_refresh_mode, uint32_t ddr4_refresh_range,uint32_t dvfsc_type);

uint32_t dwc_ddrctl_cinit_get_ddr_trfc_dlr_x32_tck(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                                   uint32_t fgr_mode, uint32_t tck_ps, uint32_t ddr5_trfc1_ps,
                                                   uint32_t ddr5_trfc2_ps, uint32_t scaled_trefi_en);


uint32_t dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                               uint32_t fgr_mode, uint32_t tck_ps);

uint32_t dwc_ddrctl_cinit_get_ddr_trfc_min_tck(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                               uint32_t fgr_mode, uint32_t tck_ps);


ddrctl_error_t ddrctl_cinit_get_ddr5_refab_sch_gap_tck(uint32_t t_rfc_min_clk,
                                                        uint32_t curr_gap_clk, uint32_t *new_gap_clk);


ddrctl_error_t ddrctl_cinit_get_ddr5_refsb_sch_gap_tck(SubsysHdlr_t *config, uint8_t pstate, uint8_t dev,
                                                   uint32_t curr_gap, uint32_t *new_gap);

#endif /* __DWC_DDRCTL_CINIT_JEDEC_DDR_TIMING_H__ */
