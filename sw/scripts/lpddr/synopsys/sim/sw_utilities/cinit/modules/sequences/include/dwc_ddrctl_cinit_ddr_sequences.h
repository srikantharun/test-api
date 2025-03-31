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


#ifndef __DWC_DDRCTL_CINIT_DDR_SEQUENCES_H__
#define __DWC_DDRCTL_CINIT_DDR_SEQUENCES_H__

#include "dwc_cinit_io.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_defines.h"
#include "sinit_types.h"

#ifdef DDRCTL_DDR
bool dwc_ddrctl_cinit_sw_seq_max_power_saving_disable(void);
bool dwc_ddrctl_cinit_sw_seq_max_power_saving_enable(void);
bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr5_entry(uint8_t target_rank);
bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr5_exit(uint8_t target_rank);
bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr4_entry(void);
bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr4_exit(void);

ddrctl_error_t dwc_ddrctl_cinit_sw_seq_ddr5_fgr_mode(SubsysHdlr_t *config, ddrctl_fgr_mode_t fgr_mode);

bool dwc_ddrctl_cinit_apply_training(void);
bool dwc_ddrctl_cinit_ddr5_init_done(uint32_t init_done, uint32_t ch);

bool dwc_ddrctl_cinit_seq_ddr4_dram_initialization(void);
bool dwc_ddrctl_cinit_seq_ddr5_dram_initialization(void);
bool dwc_ddrctl_cinit_seq_ddr5_dimm_initialization(void);
bool dwc_ddrctl_cinit_seq_ddr5_mpc(void);
bool dwc_ddrctl_cinit_seq_ddr5_prm_mr(void);


bool dwc_ddrctl_cinit_seq_ddr4_send_mrw(uint32_t mr_addr, uint32_t mr_data, uint32_t mr_rank, uint32_t ch);
bool dwc_ddrctl_cinit_pre_phyinit(void);
bool dwc_ddrctl_cinit_post_phyinit(void);
bool dwc_ddrctl_cinit_phy_lp3_io_retention(bool enter_retention);
bool dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(uint32_t mode);
bool dwc_ddrctl_cinit_seq_poll_cmd_rslt(uint32_t timeout_us, uint8_t  size, uint8_t position, uint32_t value);
bool dwc_ddrctl_cinit_seq_poll_glb_blk_events_ongoing(uint32_t value, uint32_t ch, uint32_t max_apb_reads);
bool dwc_ddrctl_cinit_seq_poll_rank_blk_events_ongoing(uint32_t value, uint32_t ch, uint32_t max_apb_reads);
bool dwc_ddrctl_cinit_seq_set_pasctl7(uint8_t value, uint8_t ch);
bool dwc_ddrctl_cinit_seq_set_pasctl8(uint32_t value, uint8_t ch);
bool dwc_ddrctl_cinit_seq_set_ddr4_mr2_asr(bool asr);
bool dwc_ddrctl_cinit_seq_ddr5_dfi_initialization(void);
#endif /* DDRCTL_DDR */

#endif /* __DWC_DDRCTL_CINIT_DDR_SEQUENCES_H__ */

