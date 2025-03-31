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


#ifndef __DWC_DDRCTL_CINIT_COMMON_SEQUENCES_H__
#define __DWC_DDRCTL_CINIT_COMMON_SEQUENCES_H__

#include "dwc_cinit_io.h"
#include "DWC_ddrctl_cc_constants.h"
#ifdef DDRCTL_SECURE
#include "DWC_ime_cc_constants.h"

#endif
#include "dwc_ddrphy_VDEFINES.h"

#ifdef DDRCTL_DDR
#include "dwc_ddrctl_cinit_ddr_sequences.h"
#endif

#ifdef DDRCTL_LPDDR
#include "dwc_ddrctl_cinit_lpddr_sequences.h"
#endif

#ifdef DDRCTL_SECURE
#include "dwc_ddrctl_cinit_ime_sequences.h"
#endif

// DWC_DDRCTL_CINIT_MLBX_TIMEOUT macro sets the maximum number of times the
// PHYINIT mailbox will be polled before a timeout error is triggered
#ifndef DWC_DDRCTL_CINIT_MLBX_TIMEOUT
  #define DWC_DDRCTL_CINIT_MLBX_TIMEOUT 500000
#endif

ddrctl_error_t dwc_ddrctl_cinit_wait_fw_done();

bool dwc_ddrctl_cinit_seq_initialization(void);
bool dwc_ddrctl_cinit_sw_seq_clocks_disable(void);
bool dwc_ddrctl_cinit_sw_seq_clocks_enable(void);
bool dwc_ddrctl_cinit_sw_seq_power_disable(void);
bool dwc_ddrctl_cinit_sw_seq_power_enable(void);
bool dwc_ddrctl_cinit_sw_seq_change_clock_frequency(void);
bool dwc_ddrctl_cinit_seq_pwr_on_rst(void);
bool dwc_ddrctl_cinit_seq_poll_operating_mode(uint32_t timeout_us, uint32_t ch, uint32_t mode);
bool dwc_ddrctl_cinit_seq_poll_selfref_type(uint32_t timeout_us, uint32_t ch, uint32_t selfref_type);
bool dwc_ddrctl_cinit_seq_poll_sw_done_ack(uint32_t value, uint32_t max_apb_reads, uint32_t ch);
bool dwc_ddrctl_cinit_seq_poll_dfi_init_complete(uint32_t value, uint32_t max_apb_reads, uint32_t ch);
bool dwc_ddrctl_cinit_seq_poll_mr_wr_busy(uint32_t value, uint32_t ch, uint32_t max_apb_reads);
bool dwc_ddrctl_cinit_seq_dfi_initialization(void);
bool dwc_ddrctl_cinit_seq_pre_qdyn_write(uint8_t ch);
bool dwc_ddrctl_cinit_seq_post_qdyn_write(uint8_t ch);
bool dwc_ddrctl_cinit_seq_enter_sw_selfref(uint32_t ch);
bool dwc_ddrctl_cinit_seq_exit_sw_selfref(uint32_t ch);
bool dwc_ddrctl_cinit_seq_set_skip_dram_init(uint32_t skp);
bool dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(uint32_t max_apb_reads);
bool dwc_ddrctl_cinit_seq_wait_ctrlr_idle(uint32_t max_apb_reads);

bool dwc_ddrctl_cinit_seq_set_opctrl1(uint8_t dis_dq, uint8_t dis_hif, uint8_t ch);
bool dwc_ddrctl_cinit_seq_initialize_ctrl_regs(void);

uint16_t dwc_ddrctl_cinit_seq_poll_mlbx(uint32_t max_apb_reads, uint32_t req_ack);


ddrctl_error_t dwc_ddrctl_cinit_phyinit(SubsysHdlr_t *cfg, ddrctl_bool_t in_restore_power_seq);

#endif /* __DWC_DDRCTL_CINIT_COMMON_SEQUENCES_H__ */
