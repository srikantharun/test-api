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


#ifndef CINIT_MODULES_VERIFICATION_INCLUDE_DDRCTL_SW_VRFY_WRAPER_H_
#define CINIT_MODULES_VERIFICATION_INCLUDE_DDRCTL_SW_VRFY_WRAPER_H_


#include "dwc_ddrctl_cinit.h"

// dwc_ddrctl_cinit_begin
void ddrctl_sw_wraper_cinit_begin(SubsysHdlr_t *vrfy_handler);
// dwc_ddrctl_cinit_main
void ddrctl_sw_wraper_cinit_main(SubsysHdlr_t *vrfy_handler);

// dwc_cinit_set_operational_clk_period
void ddrctl_sw_wraper_cinit_set_clk(SubsysHdlr_t *vrfy_handler);

// dwc_cinit_get_min_t_xsr
int unsigned ddrctl_sw_wraper_cinit_get_min_t_xsr(SubsysHdlr_t *vrfy_handler, int tck_ps, int dvfsc_type);

// dwc_ddrctl_cinit_prgm_ucode
void ddrctl_sw_wraper_cinit_prgm_ucode(SubsysHdlr_t *vrfy_handler);
// dwc_ddrctl_cinit_prgm_cfgbuf
void ddrctl_sw_wraper_cinit_prgm_cfgbuf(SubsysHdlr_t *vrfy_handler);
// dwc_ddrctl_cinit_prgm_hwffcmrw
void ddrctl_sw_wraper_cinit_prgm_hwffcmrw(SubsysHdlr_t *vrfy_handler);

// dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUT_entry
void ddrctl_sw_wraper_cinit_prgm_addr_map_lut(SubsysHdlr_t *vrfy_handler);

// dwc_cinit_phyinit_setuserinput
void ddrctl_sw_wraper_cinit_phyinit(SubsysHdlr_t *vrfy_handler);

void ddrctl_sw_wraper_cpu_dpi_main(SubsysHdlr_t *vrfy_handler, dwc_ddrctl_cinit_seq_e cinit_seq);


// dwc_ddrctl_cinit_custom_getUserInput
// dwc_ddrctl_cinit_custom_setUserInput
// dwc_ddrctl_cinit_get_stagger_ref_timing_max
// dwc_ddrctl_cinit_get_ddr_trfc_dlr_x32_tck
// dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck
// dwc_ddrctl_cinit_get_ddr_trfc_min_tck
// dwc_cinit_verf_get_cas_latency

#endif /* CINIT_MODULES_VERIFICATION_INCLUDE_DDRCTL_SW_VRFY_WRAPER_H_ */
