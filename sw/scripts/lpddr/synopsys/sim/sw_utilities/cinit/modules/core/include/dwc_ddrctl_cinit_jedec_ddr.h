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


#ifndef __DWC_DDRCTL_CINIT_JEDEC_DDR_H__
#define __DWC_DDRCTL_CINIT_JEDEC_DDR_H__

#include "dwc_ddrctl_cinit.h"

// --------------------------------------------------------------------------
// Name        : ddr4::set_clk_speed()
// Description : set the sg_tck_ps value in the hdlr->timingParams_m structure
// Params      : hdlr
// Returns     : none
// --------------------------------------------------------------------------
void ddr4_set_clk_speed(SubsysHdlr_t* hdlr, uint32_t p, uint32_t n);

// --------------------------------------------------------------------------
// Name        : ddr5::set_clk_speed()
// Description : set the sg_tck_ps value in the hdlr->timingParams_m structure
// Params      : hdlr
// Returns     : none
// --------------------------------------------------------------------------
void ddr5_set_clk_speed(SubsysHdlr_t* hdlr, uint32_t p, uint32_t n);

// --------------------------------------------------------------------------
// Name        : ddr4_set_default_timing()
// Description : set all the default values for SNPS VIP
// Returns     : ddrctl_error_t
// --------------------------------------------------------------------------
ddrctl_error_t ddr4_set_default_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n);

// --------------------------------------------------------------------------
// Name        : ddr5_set_default_timing_vip()
// Description : set all the default values for SNPS VIP
// Returns     : none
// --------------------------------------------------------------------------
void ddr5_set_default_timing(SubsysHdlr_t* hdlr, uint32_t p, uint32_t n);
// --------------------------------------------------------------------------
// Name        : ddr4_get_cas_latency()
// Description : depending on the speed grade, pick a CAS latency
// Params      : gd_en, dll_off_mode, sg
// Returns     : CAS Latency value
// --------------------------------------------------------------------------
uint32_t ddr4_get_cas_latency(uint32_t pstate, SubsysHdlr_t* hdlr, bool gd_en, bool dll_off_mode, uint32_t n);

//--------------------------------------------------------------------------
// Name        : ddr4_get_CWL_1st_set
// Description : depending on the speed grade and CAS Latency, pick the lower CAS Write Latency value
// Params      : dll_off_init, sg
// Returns     : lower possible CAS Write Latency value
//--------------------------------------------------------------------------
uint32_t ddr4_get_CWL_1st_set (uint32_t pstate, SubsysHdlr_t* hdlr, bool dll_off_init);

// --------------------------------------------------------------------------
// Name        : ddr4_get_CWL_2nd_set
// Description : depending on the speed grade and CAS Latency, pick a the upper CAS Write Latency value
// Params      : dll_off_init, sg
// Returns     : upper possible CAS Write Latency value
// --------------------------------------------------------------------------
uint32_t ddr4_get_CWL_2nd_set(uint32_t pstate, SubsysHdlr_t* hdlr, bool dll_off_init);

// --------------------------------------------------------------------------
// Name        : ddr4_get_cas_latency_rdbi()
// Description : depending on the speed grade, pick a CAS latency
// Params      : gd_en, bool dll_off_mode, dwc_ddr4_speed_grade_e sg
// Returns     : CAS Latency value with Read DBI
// --------------------------------------------------------------------------
uint32_t ddr4_get_cas_latency_rdbi(uint32_t pstate, SubsysHdlr_t* hdlr, bool gd_en, bool dll_off_mode, uint32_t n);

//--------------------------------------------------------------------------
// Name        : ddr4_get_write_recovery_time
// Description : depending on the speed grade, pick up the write recovery time
// Params      : gd_en
// Returns     : write recovery time
//--------------------------------------------------------------------------
uint32_t ddr4_get_write_recovery_time(uint32_t pstate, bool gd_en);

// --------------------------------------------------------------------------
// Name        : ddr5_get_cas_latency()
// Description : depending on the speed bin/tck, pick a CAS latency
// Params      : speed_bin: DDR5 speed bin enum value
// Params      : tck_ps_p: Current clock cycle time
// Returns     : CAS Latency value
// --------------------------------------------------------------------------
uint32_t ddr5_get_cas_latency(SubsysHdlr_t *cfg, dwc_ddr5_speed_bin_t speed_bin, uint32_t tck_ps_p);

// Minimum and maximum supported CAS LATENCY based on:
// SPD Annex L, Serial Presence Detect (SPD) for DDR4 SDRAM Modules, Release 4 section 8.1.21
#define CAS_LATENCY_DDR4_MIN 7
#define CAS_LATENCY_DDR4_MAX 52

#endif /* __DWC_DDRCTL_CINIT_JEDEC_DDR_H__ */
