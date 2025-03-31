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


#ifndef __SW_CMD_INTF_DDR5_INCLUDE_CINIT_DDR5_SW_CMD_H__
#define __SW_CMD_INTF_DDR5_INCLUDE_CINIT_DDR5_SW_CMD_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_defines.h"

typedef enum ddr5_sw_cmd_intf_e{
    SW_CTRL_INTF_MRW         = 0,
    SW_CTRL_INTF_MRR         = 1,
    SW_CTRL_INTF_SR_CTRL     = 2,
    SW_CTRL_INTF_PD_CTRL     = 3,
    SW_CTRL_INTF_RST_CTRL    = 4,
    SW_CTRL_INTF_MPC         = 5,
    SW_CTRL_INTF_PRE         = 6,
    SW_CTRL_INTF_REF         = 7,
    SW_CTRL_INTF_VREF        = 8,
    SW_CTRL_INTF_NOP         = 9,
    SW_CTRL_INTF_DES         = 10, // 0x0a
    SW_CTRL_INTF_DISDQREF    = 11, // 0x0b
    SW_CTRL_INTF_FORCECS     = 12, // 0x0c
    SW_CTRL_INTF_OPCTRL      = 13, // 0x0d
    SW_CTRL_INTF_RFM         = 14, // 0x0e
    SW_CTRL_INTF_ACT         = 16, // 0x10
    SW_CTRL_INTF_RD          = 17, // 0x11
    SW_CTRL_INTF_WR          = 18, // 0x12
    SW_CTRL_INTF_WRP         = 19, // 0x13
    SW_CTRL_INTF_DFIUPD      = 21, // 0x15
    SW_CTRL_INTF_DFILP       = 22, // 0x16
    SW_CTRL_INTF_DFIFC       = 23, // 0x17
    SW_CTRL_INTF_LOCK_CTRL   = 24, // 0x18
    SW_CTRL_INTF_DFICLK      = 25, // 0x19
    SW_CTRL_INTF_DFI_2N_MODE = 26, // 0x2a
    SW_CTRL_INTF_REF_FLUSH   = 27  // 0x2b
} ddrctl_ddr5_sw_cmd_intf_t;


typedef enum ddrctl_sw_cmd_last_e{
    SW_CTRL_LAST_CMD         = 1,
    SW_CTRL_NOT_LAST_CMD     = 0
} ddrctl_sw_cmd_last_t;


typedef enum cinit_sw_cmd_disdref_type_e{
    SW_CMD_DISDQREF_TYPE_PAUSE = 0x0,
    SW_CMD_DISDQREF_TYPE_BLOCK = 0x1,
} cinit_sw_cmd_disdqref_type_t;

static inline const char * ddrctl_sw_cmd_disdqref_type_str(cinit_sw_cmd_disdqref_type_t type)
{
    switch (type) {
        case SW_CMD_DISDQREF_TYPE_PAUSE:
            return "Pause";
        case SW_CMD_DISDQREF_TYPE_BLOCK:
        default:
            return "Block";
    }
}

typedef enum cinit_sw_cmd_sr_ctrl_type_e{
    SW_CMD_SR_CTRL_FC_SRE_CMD      = 0x0,
    SW_CMD_SR_CTRL_FC_SREF_SRX_CMD = 0x1
} cinit_sw_cmd_sr_ctrl_type_t;

static inline const char * ddrctl_sw_cmd_sr_ctrl_type_str(cinit_sw_cmd_sr_ctrl_type_t type)
{
    switch (type) {
        case SW_CMD_SR_CTRL_FC_SREF_SRX_CMD:
            return "SREF";
        case SW_CMD_SR_CTRL_FC_SRE_CMD:
        default:
            return "SRE";
    }
}

const char* ddrctl_cinit_get_ddr5_sw_cmd_str(const ddrctl_ddr5_sw_cmd_intf_t sw_cmd);

ddrctl_error_t cinit_ddr5_send_mrw(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                   uint8_t address, uint8_t data, ddrctl_bool_t ctrl_word,
                                   ddrctl_bool_t dual_die_pkg, uint8_t active_ranks_map,
                                   ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_mrr(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                   uint8_t rank_num, uint8_t address, ddrctl_bool_t dual_die_pkg,
                                   ddrctl_status_t phy_snoop, ddrctl_status_t pause_ref,
                                   ddrctl_status_t tcr_update, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_self_refresh_control(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                                    uint8_t active_ranks_map, cinit_sw_cmd_sr_ctrl_type_t cmd,
                                                    ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_reset_control(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                             ddrctl_status_t status, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_mpc(SubsysHdlr_t *cfg, ddrctl_channel_t channel, ddrctl_bool_t dual_die_pkg,
                                   uint8_t op, ddrctl_status_t pause_ref, uint8_t active_ranks_map,
                                   ddrctl_status_t multi_cyc_cs, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_nop(SubsysHdlr_t *cfg, ddrctl_channel_t channel, uint16_t count,
                                   uint8_t active_ranks_map, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_disable_dq_refresh(SubsysHdlr_t *cfg, ddrctl_channel_t channel, uint8_t dq_set,
                                                   uint8_t dq_reset, uint8_t refresh_set, uint8_t refresh_reset,
                                                   cinit_sw_cmd_disdqref_type_t refresh_type,
                                                   ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_force_cs(SubsysHdlr_t *cfg, ddrctl_channel_t channel, uint8_t cs_force,
                                         uint8_t cs_release, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_preab(SubsysHdlr_t *cfg);

ddrctl_error_t cinit_ddr5_send_refab(SubsysHdlr_t *cfg, uint8_t ranks_map, uint32_t cmd_int_ns);

ddrctl_error_t cinit_ddr5_send_op_ctrl(SubsysHdlr_t *cfg, ddrctl_channel_t channel, uint8_t srx_done_txsdll,
                                       uint8_t srx_done_txs, uint8_t pdx_done, uint8_t mpsmx_done,
                                       uint8_t non_target_odt_en, uint8_t non_target_odt_dis,
                                       ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_dfi_ctrlupd(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                       ddrctl_status_t upd_request, ddrctl_status_t upd_retry, uint8_t num_retries,
                                       ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_dfi_freq_chg_ctrl(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                                 uint8_t init_start, uint8_t init_clear, uint8_t freq_ratio,
                                                 uint8_t freq, uint8_t freq_fsp, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_dfi_clock_ctrl(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                              ddrctl_status_t status, uint8_t active_ranks_map,
                                              ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_ctl_dfi_2n_mode(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                               ddrctl_status_t status, ddrctl_sw_cmd_last_t last_cmd);

ddrctl_error_t cinit_ddr5_send_ref_flush(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                         uint8_t active_ranks_map);

#endif  //__SW_CMD_INTF_DDR5_INCLUDE_CINIT_DDR5_SW_CMD_H__


