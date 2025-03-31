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


#ifndef __DWC_DDRCTL_CINIT_LPDDR_SEQUENCES_H__
#define __DWC_DDRCTL_CINIT_LPDDR_SEQUENCES_H__

#include "dwc_cinit_io.h"
#include "dwc_ddrctl_cinit.h"

#ifdef DDRCTL_LPDDR
// Define a waiting timeout value (in clock cycles) used in LPDDR5 SW self refresh with retraining followed by PPT2
#define DWC_DDRCTL_LPDDR5_SW_SREF_PPT2_DELAY 1024

bool dwc_ddrctl_cinit_seq_lpddr4_dram_initialization(void);
bool dwc_ddrctl_cinit_seq_lpddr5_dram_initialization(void);
bool dwc_ddrctl_cinit_seq_mr_access(bool is_rd,uint32_t mr_address, uint32_t mr_data, uint32_t rank, bool sw_init_int, uint32_t ch);
bool dwc_ddrctl_cinit_seq_enter_dsm(uint32_t ch, uint32_t freq);
bool dwc_ddrctl_cinit_seq_exit_dsm(uint32_t ch, uint32_t freq);
bool dwc_ddrctl_cinit_seq_poll_selfref_state(uint32_t max_apb_reads, uint32_t ch, uint32_t state);
bool dwc_ddrctl_cinit_seq_poll_dqsosc_state(uint32_t max_apb_reads, uint32_t ch, uint32_t state);
bool dwc_ddrctl_cinit_phy_lp3_io_retention(bool);
bool dwc_ddrctl_cinit_seq_lpddr5_halt_zqcal(void);
bool dwc_ddrctl_cinit_seq_lpddr5_resume_zqcal(void);
bool dwc_ddrctl_cinit_seq_swffc_with_fsp(uint32_t target_freq);
bool dwc_ddrctl_cinit_seq_lpddr_sw_zqcal(uint32_t ch);
bool dwc_ddrctl_cinit_seq_poll_zq_calib_short_busy(uint32_t value, uint32_t ch, uint32_t max_apb_reads);
bool dwc_ddrctl_cinit_seq_wait_operating_mode(uint32_t timer, uint32_t ch, uint32_t exp_val);
bool dwc_ddrctl_cinit_sw_seq_change_rfm_level(uint32_t rfm_level);
bool dwc_ddrctl_cinit_sw_seq_selfref_with_retrain_ppt2(void);

#endif /* DDRCTL_LPDDR */

#endif /* __DWC_DDRCTL_CINIT_LPDDR_SEQUENCES_H__ */
