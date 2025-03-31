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


#include "physetup.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_cinit_macros.h"
#include "bit_macros.h"
#include "mode_regs/ddr5/ddrctl_sw_ddr5_mode_regs.h"
#include "mode_regs/ddr4/ddrctl_sw_ddr4_mode_regs.h"
#include "ctrl_words/ddr5/cinit_ddr5_ctrl_words.h"
#include "ctrl_words/ddr4/ddrctl_sw_ddr4_ctrl_words.h"
#include "dwc_ddrctl_cinit_defines.h"


#ifdef DDRCTL_DDR
#ifndef DDR5_PHY

#define CINIT_MAX_CMD_STR   100
#define TRAIN_2D_DISABLE    0

ddrctl_error_t ddr5_get_dqs_osc_run_time(uint16_t rm45_osc_run_time, uint16_t *osc_run_time)
{
    if ((16 == rm45_osc_run_time) || (32 == rm45_osc_run_time)) {
        *osc_run_time = rm45_osc_run_time * 16;
    } else if (rm45_osc_run_time == 63) {
        *osc_run_time = 1024;
    } else if ((rm45_osc_run_time >= 64) && (rm45_osc_run_time <= 127)) {
        *osc_run_time = 2048;
    } else if ((rm45_osc_run_time >= 128) && (rm45_osc_run_time <= 191)) {
        *osc_run_time = 4096;
    } else if ((rm45_osc_run_time >= 192) && (rm45_osc_run_time <= 255)) {
        *osc_run_time = 8192;
    } else {
        SNPS_ERROR("rm45.dqosc_runtime=0x%0x is not supported by PHY", rm45_osc_run_time);
        return DDRCTL_ERROR;
    }

    return DDRCTL_SUCCESS;
}


void ddr5_get_num_active_dbyte(SubsysHdlr_t *cfg, uint32_t *num_dbyte_dfi0, uint32_t *num_dbyte_dfi1)
{
    uint32_t num_active_dbyte_dfi0;
    uint32_t num_active_dbyte_dfi1;
#ifdef DDRCTL_DDR_DRAM_ECC_WIDTH_GT_0
    if (cfg->dfi1_exists) {
        if (IS_DUAL_CHAN) {
            num_active_dbyte_dfi0 = DIV_2(cfg->num_dbytes);
            num_active_dbyte_dfi1 = DIV_2(cfg->num_dbytes);
        } else {
#ifdef DDRCTL_DDR_DCH_HBW_1
            num_active_dbyte_dfi0 = cfg->num_dbytes;
#else // Not DDRCTL_DDR_DCH_HBW_1
            num_active_dbyte_dfi0 = DIV_2(cfg->num_dbytes);
#endif // DDRCTL_DDR_DCH_HBW_1
            num_active_dbyte_dfi1 = 0;
        }
    } else {
        if ((DWC_DDRCTL_NUM_CHANNEL == 2) && (REGB_DDRC_CH0.chctl.dual_channel_en == 0)) {
            num_active_dbyte_dfi0 = DIV_2(cfg->num_dbytes);
        } else {
            num_active_dbyte_dfi0 = cfg->num_dbytes;
        }
        num_active_dbyte_dfi1 = 0;
    }
#else
    if(cfg->dfi1_exists) {
        if(IS_DUAL_CHAN) {
            num_active_dbyte_dfi0 = DIV_2(cfg->num_dbytes);
            num_active_dbyte_dfi1 = DIV_2(cfg->num_dbytes);
  #ifdef DDRCTL_DDR_DCH_HBW_1
            if(cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_QUARTER) {
                num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
                num_active_dbyte_dfi1 = DIV_2(num_active_dbyte_dfi1);
            }
  #else // Not DDRCTL_DDR_DCH_HBW_1
            if(cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
                num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
                num_active_dbyte_dfi1 = DIV_2(num_active_dbyte_dfi1);
            }
  #endif // DDRCTL_DDR_DCH_HBW_1
        } else {
            num_active_dbyte_dfi0 = DIV_2(cfg->num_dbytes);
            num_active_dbyte_dfi1 = 0;
  #ifdef DDRCTL_DDR_DCH_HBW_1
            if(cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_QUARTER) {
                num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
            }
  #else // Not DDRCTL_DDR_DCH_HBW_1
            if(cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
                num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
            }
  #endif // DDRCTL_DDR_DCH_HBW_1
        }
    } else {
        if( cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL ) {
            num_active_dbyte_dfi0 = cfg->num_dbytes;
        } else if(cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF ) {
            num_active_dbyte_dfi0 = DIV_2(cfg->num_dbytes);
        } else {
            num_active_dbyte_dfi0 = DIV_4(cfg->num_dbytes);
        }
        num_active_dbyte_dfi1 = 0;
    }
#endif
    *num_dbyte_dfi0 = num_active_dbyte_dfi0;
    *num_dbyte_dfi1 = num_active_dbyte_dfi1;
}


uint32_t ddr5_get_t_staoff_ps(SubsysHdlr_t *cfg, uint8_t  pstate)
{
    uint32_t rcd_tstaoff_ps;

    if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) {
        // CASE 01050020 From VIP team tSTAOFF_ps = tPDM_ps + 0.5*tCK_ps
        rcd_tstaoff_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tpdm_ps;
        rcd_tstaoff_ps += DIV_2(cfg->spdData_m.tck_ps[pstate]) + 2;

#ifndef DWC_PHYINIT_RID_GE202206
        if (cfg->memCtrlr_m.ddr5_mr[0].mr2.ddr5_2n_mode == DDR5_MR2_2N_MODE) { // 2N mode
#ifdef DWC_PHYINIT_RID_GE202008
            rcd_tstaoff_ps = rcd_tstaoff_ps - DIV_2(cfg->spdData_m.tck_ps[pstate]); // -1UI for SDR2 mode as a workaround
#endif
            if (cfg->ddr5_cw.rw00.sdr_mode == 0) {
                rcd_tstaoff_ps += cfg->spdData_m.tck_ps[pstate]; // Adjust for TxDly
            }
        } else {
            rcd_tstaoff_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tpdm_ps + cfg->spdData_m.tck_ps[pstate] + 2; // Adjust for TxDly
        }
#endif
    } else if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
#ifdef DWC_PHYINIT_RID_GE202206
        rcd_tstaoff_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tpdm_ps + DIV_2(cfg->spdData_m.tck_ps[pstate]) + 2;
#else
        if (cfg->memCtrlr_m.ddr5_mr[0].mr2.ddr5_2n_mode == DDR5_MR2_2N_MODE) { // 2N mode
#ifdef DWC_PHYINIT_RID_GE202008
            rcd_tstaoff_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tstaoff_ps + 2 - DIV_2(cfg->spdData_m.tck_ps[pstate]); // -1UI for SDR2 mode as a workaround
#else
            rcd_tstaoff_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tstaoff_ps + 2; // Adjust for TxDly
#endif
        } else {
            rcd_tstaoff_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tstaoff_ps + 2; // Adjust for TxDly
        }
#endif
    }
    SNPS_LOG("rcd_tstaoff_ps[%d] = %0u", pstate, rcd_tstaoff_ps);

    return rcd_tstaoff_ps;
}


uint8_t ddr5_get_enable_dqs(SubsysHdlr_t *cfg, uint8_t  channel)
{
    uint8_t enableddq;
#ifdef DDRCTL_DDR_DRAM_ECC_WIDTH_GT_0
        if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_UDIMM) {
            enableddq = 0x24;
        } else if (((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) || (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM))
                    && cfg->spdData_m.ddr5_dimm_ch_arch == DATA_CHANNEL_36_BIT) {
            enableddq = 0x24;
        } else {
            enableddq = 0x28;
        }
#else
        enableddq = 0x20;
#endif

        //For single DFI channel, EnabledDQsChB and CsPresentChB shoule be set to 0x0
        if (channel == 0) {
            return enableddq;
        } else {
            if (IS_DUAL_CHAN) {
                return enableddq;
            } else {
                return 0;
            }
        }
}


uint8_t get_dimm_type(SubsysHdlr_t *cfg)
{
    switch (DDRCTL_GET_DIMM_TYPE(cfg, 0)) {
        case DWC_UDIMM:
            return 0;
        case DWC_RDIMM:
            return 2;
        case DWC_LRDIMM:
            return 3;
        case DWC_NODIMM:
            return 4;
        default:
            SNPS_ERROR("DIMM type not supported %d", DDRCTL_GET_DIMM_TYPE(cfg, 0));
    }
    return 4;
}


void ddrctl_sw_phyinit_ddr5_config(SubsysHdlr_t *cfg)
{
#ifdef MEMC_DDR5
#ifdef CINIT_DDR5
    char        cmd_str[CINIT_MAX_CMD_STR];
    uint8_t     channel;
    uint8_t     pstate;
    uint8_t     freq_ratio;
#ifndef DWC_PHYINIT_RID_GE202206
    uint8_t     is_2n_mode;
#endif
    uint8_t     cs_present_cha;
    uint8_t     cs_present_chb;
    uint8_t     mr_value;
    uint16_t    disabled_dbyte;
    uint16_t    wl_adj_start;
    uint16_t    wl_adj_end;
    uint16_t    dqsosc_runtime;
    uint32_t    msgmisc;
    uint32_t    d5misc;
    uint32_t    num_active_dbyte_dfi0;
    uint32_t    num_active_dbyte_dfi1;
    uint32_t    ddr5_rcd_tpdm_rd_ps;
    uint32_t    ddr5_rcd_tpdm_wr_ps;
    ddrctl_bool_t           disable_re_training;
    ddrctl_bool_t           is_capar_retry_enable;
    ddrctl_error_t          rslt;
    ddr5_mode_registers_t   *mr;

    physetup_set_user_input(cfg, "DramType", DWC_DDR5);
    physetup_set_user_input(cfg, "NumPStates", cfg->num_pstates);
    physetup_set_user_input(cfg, "Dfi1Exists", cfg->dfi1_exists);

    rslt = ddr5_get_dqs_osc_run_time(cfg->memCtrlr_m.ddr5_mr[0].mr45.osc_run_time, &dqsosc_runtime);
    if (DDRCTL_SUCCESS != rslt) {
        dwc_ddrctl_cinit_exit(1);
    }

#ifdef DWC_PHYINIT_RID_GE202201
    if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_NODIMM) {
        physetup_set_user_input(cfg, "Nibble_ECC", 0);
    }
#endif

    // PHY-initiated re-training is enabled only for DDR5 phy training case.
    if (cfg->phy_training == DWC_PHY_TRAINING) {
        disable_re_training = DDRCTL_FALSE;    //Enable PPT
        cfg->memCtrlr_m.ddr5_mr[0].mr2.cs_assertion_duration = 1;
    } else {
        disable_re_training = DDRCTL_TRUE;    //Disable PPT
    }
    physetup_set_user_input(cfg, "D5DisableRetraining", disable_re_training);


#ifdef DWC_PHYINIT_RID_GE202008
    for(pstate=0;pstate<cfg->num_pstates;pstate++) {
        snprintf (cmd_str, CINIT_MAX_CMD_STR, "DqsOscRunTimeSel[%d]", pstate);
        physetup_set_user_input (cfg, cmd_str, dqsosc_runtime);
    }
#else
        physetup_set_user_input(cfg, "DqsOscRunTimeSel", dqsosc_runtime);
#endif

#ifdef DWC_PHYINIT_RID_GE202301
    if ((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_UDIMM) &&
        (DWC_DDRCTL_NUM_CHANNEL == 2) &&
        (REGB_DDRC_CH0.chctl.dual_channel_en == 0) )  {
        physetup_set_user_input(cfg, "PowerDownANIBs", 0x0140); // Power Down ACXs 6/8 which generate clocks for Channel B
    }
#endif

    ddr5_get_num_active_dbyte(cfg, &num_active_dbyte_dfi0, &num_active_dbyte_dfi1);

    physetup_set_user_input(cfg, "NumActiveDbyteDfi0", num_active_dbyte_dfi0);
    physetup_set_user_input(cfg, "NumActiveDbyteDfi1", num_active_dbyte_dfi1);

    physetup_set_user_input(cfg, "NumRank_dfi0", cfg->spdData_m.num_ranks);
    if (IS_DUAL_CHAN) {
        physetup_set_user_input(cfg, "NumRank_dfi1", cfg->spdData_m.num_ranks);
    } else {
        physetup_set_user_input(cfg, "NumRank_dfi1", 0);
    }

    physetup_set_user_input(cfg, "NumAnib", cfg->num_anibs);
    physetup_set_user_input(cfg, "NumDbyte", cfg->num_dbytes);

    physetup_set_user_input(cfg, "DimmType", get_dimm_type(cfg));

#ifdef DWC_PHYINIT_RID_GE202201
    physetup_set_user_input(cfg, "DramDataWidth[0]", cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input(cfg, "DramDataWidth[1]", cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input(cfg, "DramDataWidth[2]", cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input(cfg, "DramDataWidth[3]", cfg->spdData_m.sdram_width_bits[0]);
#else
    physetup_set_user_input (cfg, "DramDataWidth", cfg->spdData_m.sdram_width_bits[0]);
#endif

    for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
        if (ddrctl_sw_get_ratio(cfg, pstate) == DWC_RATIO_1_2) {
            freq_ratio = 1;
        } else {
            freq_ratio = 2;
        }
        snprintf (cmd_str, CINIT_MAX_CMD_STR, "DfiFreqRatio[%d]", pstate);
        physetup_set_user_input(cfg, cmd_str, freq_ratio);
    }

    for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
        uint32_t tck_ps = cfg->spdData_m.tck_ps[pstate];
        uint32_t freq;
#ifdef DWC_PHYINIT_RID_GE202102
        // VIP interprets 333 as 6000 Mbps, PHY as 6006 Mbps, For RD CRC - CL is increased by 2 ifMbps > 6000, increase by 1 to align VIP + PHY
        // VIP interprets 312 as 6400 Mbps, PHY as 6410 Mbps, For RD CRC - CL is increased by 2 ifMbps < 6400, increase by 1 to align VIP + PHY
        if ((tck_ps == 333) || (tck_ps == 312) ||
            (tck_ps == 294) || (tck_ps == 277) ||
            (tck_ps == 263) || (tck_ps == 250) ||
            (tck_ps == 238) ) {
            tck_ps=tck_ps + 1;
        }
#endif
        freq = CEIL(1000000, tck_ps);
        snprintf (cmd_str, CINIT_MAX_CMD_STR, "Frequency[%d]", pstate);
        physetup_set_user_input(cfg, cmd_str, freq);
    }

    physetup_set_user_input(cfg, "PllBypass[0]", REGB_DDRC_CH0.mstr0.dll_off_mode);
    physetup_set_user_input(cfg, "PllBypass[1]", 0);  // TODO
    physetup_set_user_input(cfg, "PllBypass[2]", 0);  // TODO
    physetup_set_user_input(cfg, "PllBypass[3]", 0);  // TODO

#ifndef DWC_PHYINIT_RID_GE202001
    physetup_set_user_input(cfg, "D5ReadCRCEnable", REGB_DDRC_CH0.crcparctl1.rd_crc_enable);
#endif

#ifndef DWC_PHYINIT_RID_GE201904
    physetup_set_user_input(cfg, "D5RxDqsPreambleCtrl[0]", 1);
    physetup_set_user_input(cfg, "D5RxDqsPreambleCtrl[1]", 1);
    physetup_set_user_input(cfg, "D5RxDqsPreambleCtrl[2]", 1);
    physetup_set_user_input(cfg, "D5RxDqsPreambleCtrl[3]", 1);
#endif

    if ((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) || (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM)) {
        // only implement disable EnTdqs2dqTrackingTg*/EnRxDqsTracking*
        // in following:
        // - DDR5
        // - RDIMM or LRDIMM
        // - if any channel has capar_retry_enable=1
        is_capar_retry_enable = DDRCTL_FALSE;

        for (channel = 0; channel < cfg->num_dch; channel++) {
            if (cfg->memCtrlr_m.static_cfg.capar_retry_enable[channel] == 1) {
                is_capar_retry_enable = DDRCTL_TRUE;
            }
        }

        if (DDRCTL_TRUE == is_capar_retry_enable) {
            SNPS_DEBUG("CA parity retry enabled when CA parity error occurs");
            // see Mantis 62220/59229
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg0[0]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg1[0]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg2[0]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg3[0]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg0[1]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg1[1]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg2[1]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg3[1]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg0[2]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg1[2]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg2[2]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg3[2]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg0[3]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg1[3]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg2[3]", 0);
            physetup_set_user_input(cfg, "EnTdqs2dqTrackingTg3[3]", 0);
            physetup_set_user_input(cfg, "EnRxDqsTracking[0]", 0);
            physetup_set_user_input(cfg, "EnRxDqsTracking[1]", 0);
            physetup_set_user_input(cfg, "EnRxDqsTracking[2]", 0);
            physetup_set_user_input(cfg, "EnRxDqsTracking[3]", 0);
        }
    }

    physetup_set_user_input(cfg, "MemAlertEn", 1); // allow dfi_alert_n to be driven to the controller
#ifdef DWC_PHYINIT_RID_GE202008
    physetup_set_user_input(cfg, "EnableMAlertAsync",REGB_DDRC_CH0.crcparctl1.dfi_alert_async_mode); //allow async alert
#endif
    physetup_set_user_input(cfg, "DisablePmuEcc", 1); //disabled the SRAM ECC feature temporarily

    if ((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) || (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM)) {
#ifndef DWC_PHYINIT_RID_GE202206

        if (cfg->memCtrlr_m.ddr5_mr[0].mr2.ddr5_2n_mode == DDR5_MR2_1N_MODE) { // 1N mode
            is_2n_mode = 0;
        } else { // 2N mode
            is_2n_mode = 1;
        }
#endif
#ifndef DWC_PHYINIT_RID_GE202001
        physetup_set_user_input(cfg, "D5RdimmSDRmode", is_2n_mode);
#endif
        if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) {
            for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "tSTAOFF[%d]", pstate);
                physetup_set_user_input(cfg, cmd_str, ddr5_get_t_staoff_ps(cfg, pstate));
            }

            for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "tPDM[%d]", pstate);
                physetup_set_user_input(cfg, cmd_str, cfg->timingParams_m[0][0].ddr5_rcd_tpdm_ps);
            }
        } // DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM

        /// Work around for PHY get wrong read data in some case
        physetup_set_user_input(cfg, "tDQSCK", cfg->spdData_m.tck_ps[0] >= 625 ? 2: 1);
    } // RDIMM || LRDIMM

    // align tDQS2DQ with value set in the VIP
    SNPS_LOG("Setting tDQS2DQ  to %0ups", cfg->timingParams_m[0][0].ddr5_tdqs2dq_ps);
    physetup_set_user_input(cfg, "tDQS2DQ", cfg->timingParams_m[0][0].ddr5_tdqs2dq_ps);


    if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
        for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
            snprintf (cmd_str, CINIT_MAX_CMD_STR, "tSTAOFF[%d]", pstate);
            physetup_set_user_input(cfg, cmd_str, ddr5_get_t_staoff_ps(cfg, pstate));
        }

        // set tPDM/tPDM_Rd id DDR5 LRDIMM
        for(pstate=0; pstate<cfg->num_pstates; pstate++) {
            ddr5_rcd_tpdm_rd_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tpdm_rd_ps;
            ddr5_rcd_tpdm_wr_ps = cfg->timingParams_m[pstate][0].ddr5_rcd_tpdm_wr_ps;
#ifndef DWC_PHYINIT_RID_GE202206
            if((is_2n_mode)&& (cfg->ddr5_cw.rw00.sdr_mode==0)) {
                ddr5_rcd_tpdm_rd_ps = ddr5_rcd_tpdm_rd_ps + cfg->spdData_m.tck_ps[pstate];
                ddr5_rcd_tpdm_wr_ps = ddr5_rcd_tpdm_wr_ps - cfg->spdData_m.tck_ps[pstate];
            }
#endif
            snprintf (cmd_str, CINIT_MAX_CMD_STR, "tPDM[%d]", pstate);
            physetup_set_user_input(cfg, cmd_str, ddr5_rcd_tpdm_wr_ps);
            snprintf (cmd_str, CINIT_MAX_CMD_STR, "tPDM_Rd[%d]", pstate);
            physetup_set_user_input(cfg, cmd_str, ddr5_rcd_tpdm_rd_ps);
        } // for pstate

    }

    disabled_dbyte = 0;
    if (cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_QUARTER) {
        disabled_dbyte = 0xcc;
    } else if (cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_HALF) {
        if (MEMC_DRAM_DATA_WIDTH == 32) {
            disabled_dbyte = 0xcc;
        }
    }

    if (cfg->spdData_m.num_ranks == 4) {
        cs_present_cha = 0xf;
    } else if (cfg->spdData_m.num_ranks == 2) {
        if ((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM)  ||
            (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) ||
            (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_UDIMM)) {
            if (cfg->spdData_m.num_ranks_per_dimm == 1) { // 1 rank rdimm *2
                cs_present_cha = 0x5;
            } else {
                cs_present_cha = 0x3;
            }
        } else { // NODIMM
            cs_present_cha = 0x3;
        }
    } else { // 1 rank
        cs_present_cha = 0x1;
    }


    if (IS_DUAL_CHAN) {
        cs_present_chb = cs_present_cha;
    } else {
        cs_present_chb = 0;
    }

    //#############################################################################
    //
    // Structure for user input simulation options
    //
    //#############################################################################

    //
    //
    // Setup the message block.
    // MsgMisc[0]: MTESTEnable
    // MsgMisc[1]: SimulationOnlyReset
    // MsgMisc[2]: SimulationOnlyTraining
    // MsgMisc[3]: UseDdr4PerDeviceVrefDq (DDR4 UDIMM/RDIMM only)
    // MsgMisc[4]: Suppress streaming messages
    // MsgMisc[5]: PerByteMaxRdLat
    // MsgMisc[6]: PartialRank
    // MsgMisc[7]: RFU
    //
    msgmisc = 0;
    if (cfg->use_jedec_init == 0) {
        msgmisc |= 1 << 1;
    }
    msgmisc |= 1 << 2;

#ifdef UMCTL2_SHARED_AC
    msgmisc |= 1 << 6;
#endif

    d5misc = 1; //PHY internal registers control memreset during training, and also after training
    d5misc |= 1 << 2; //Use_back2back_MRR
    d5misc |= 1 << 6; //Train also CK ANIB delay during CS/CA training

    for (pstate = 0; pstate < cfg->num_pstates; pstate++) {

        physetup_set_msg_block(cfg, pstate, "MsgMisc", msgmisc, TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "HdtCtrl", cfg->HdtCtrl, TRAIN_2D_DISABLE); // Stage completion
        physetup_set_msg_block(cfg, pstate, "DFIMRLMargin", 1, TRAIN_2D_DISABLE);

        mr = &(cfg->memCtrlr_m.ddr5_mr[pstate]);

        switch (mr->mr8.wr_preamble) {
            case 1:
                wl_adj_start = 96;
                wl_adj_end = 160;
                break;
            case 2:
                wl_adj_start = 160;
                wl_adj_end = 224;
                break;
            case 3:
                wl_adj_start = 288;
                wl_adj_end = 352;
                break;
            default:
                wl_adj_start = 0;
                wl_adj_end = 0;
                break;
        }

        physetup_set_msg_block(cfg, pstate, "D5Misc", d5misc, TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "DRAMFreq",
                (CEIL(2000000, cfg->spdData_m.tck_ps[pstate])), TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "DFIMRLMargin", 0x1, TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "DisabledDbyte", disabled_dbyte, TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "WL_ADJ_START", wl_adj_start, TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "WL_ADJ_END", wl_adj_end, TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "EnabledDQsChA", ddr5_get_enable_dqs(cfg, 0), TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "EnabledDQsChB", ddr5_get_enable_dqs(cfg, 1), TRAIN_2D_DISABLE);
        physetup_set_msg_block(cfg, pstate, "MR0_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 0), 0);
#ifdef DWC_PHYINIT_RID_GE202001
        physetup_set_msg_block(cfg, pstate, "MR2_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 2), 0);
#endif
        physetup_set_msg_block(cfg, pstate, "MR4_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 4), 0);
        physetup_set_msg_block(cfg, pstate, "MR5_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 5), 0);
        physetup_set_msg_block(cfg, pstate, "MR6_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 6), 0);
        physetup_set_msg_block(cfg, pstate, "MR8_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 8), 0);
#ifdef DWC_PHYINIT_RID_GE202001
        physetup_set_msg_block(cfg, pstate, "MR13_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 13), 0);
#endif
        physetup_set_msg_block(cfg, pstate, "MR34_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 34), 0);
        physetup_set_msg_block(cfg, pstate, "MR35_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 35), 0);
        physetup_set_msg_block(cfg, pstate, "MR37_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 37), 0);
        physetup_set_msg_block(cfg, pstate, "MR38_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 38), 0);

        physetup_set_msg_block(cfg, pstate, "MR39_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 39), 0);
#ifndef DWC_PHYINIT_RID_GE202102
        physetup_set_msg_block(cfg, pstate, "MR40_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 40), 0);
#endif
        physetup_set_msg_block(cfg, pstate, "MR50_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 50), 0);
        physetup_set_msg_block(cfg, pstate, "MR51_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 51), 0);
        physetup_set_msg_block(cfg, pstate, "MR52_A0", ddrctl_sw_get_ddr5_mode_reg(cfg, pstate, 52), 0);
        physetup_set_msg_block(cfg, pstate, "UseBroadcastMR", 1, 0);

        /**  TODO Jira P80001562-309341, Case 01440643, DDR5 UDIMM/NODIMM CA training issue, For 3DS or 64Gb devices, set CATrainOpt[4]=0*/
        SNPS_DEBUG("CID width[0] = %0d", cfg->spdData_m.cid_width[0]);
        SNPS_DEBUG("Density = %0d", cfg->spdData_m.sdram_capacity_mbits[0]);
        // 3DS or 64GBIT
        if ((cfg->spdData_m.cid_width[0] > 0) || (DDRCTL_GET_MEM_DENSITY(cfg, 0) == CINIT_64GBIT)) {
            physetup_set_msg_block(cfg, pstate, "CATrainOpt", 0xc, 0);
        } else {
            physetup_set_msg_block(cfg, pstate, "CATrainOpt", 0x1c, 0);
        }

        physetup_set_msg_block(cfg, pstate, "RX2D_TrainOpt", 0x1e, 0);
        physetup_set_msg_block(cfg, pstate, "TX2D_TrainOpt", 0x1e, 0);
        physetup_set_msg_block(cfg, pstate, "CsPresentChA", cs_present_cha, 0);
        physetup_set_msg_block(cfg, pstate, "CsPresentChB", cs_present_chb, 0);

        if ((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) || (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM)) {
            mr_value = ddrctl_sw_get_ddr5_ctrl_word(cfg, pstate, 0x00);
            physetup_set_msg_block(cfg, pstate, "RCW00_ChA_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW00_ChA_D1", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW00_ChB_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW00_ChB_D1", mr_value, 0);
            mr_value = ddrctl_sw_get_ddr5_ctrl_word(cfg, pstate, 0x05);
            physetup_set_msg_block(cfg, pstate, "RCW05_ChA_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW05_ChA_D1", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW05_ChB_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW05_ChB_D1", mr_value, 0);
            mr_value = ddrctl_sw_get_ddr5_ctrl_word(cfg, pstate, 0x11);
            physetup_set_msg_block(cfg, pstate, "RCW11_ChA_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW11_ChA_D1", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW11_ChB_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW11_ChB_D1", mr_value, 0);
            mr_value = ddrctl_sw_get_ddr5_ctrl_word(cfg, pstate, 0x01);
            physetup_set_msg_block(cfg, pstate, "RCW01_ChA_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW01_ChA_D1", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW01_ChB_D0", mr_value, 0);
            physetup_set_msg_block(cfg, pstate, "RCW01_ChB_D1", mr_value, 0);
        }

        if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
            physetup_set_msg_block(cfg, pstate, "BCW68_ChA_D0", 0x44, 0);//PG[b]E0,configured the default value
            physetup_set_msg_block(cfg, pstate, "BCW68_ChA_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW68_ChB_D0", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW68_ChB_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW69_ChA_D0", 0x44, 0);//PG[b]E1
            physetup_set_msg_block(cfg, pstate, "BCW69_ChA_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW69_ChB_D0", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW69_ChB_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6A_ChA_D0", 0x55, 0);//PG[b]E2
            physetup_set_msg_block(cfg, pstate, "BCW6A_ChA_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6A_ChB_D0", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6A_ChB_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6B_ChA_D0", 0x55, 0);//PG[b]E3
            physetup_set_msg_block(cfg, pstate, "BCW6B_ChA_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6B_ChB_D0", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6B_ChB_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6C_ChA_D0", 0x44, 0);//PG[b]E4
            physetup_set_msg_block(cfg, pstate, "BCW6C_ChA_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6C_ChB_D0", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6C_ChB_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6D_ChA_D0", 0x55, 0);//PG[b]E5
            physetup_set_msg_block(cfg, pstate, "BCW6D_ChA_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6D_ChB_D0", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6D_ChB_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6E_ChA_D0", 0x44, 0);//PG[b]E6
            physetup_set_msg_block(cfg, pstate, "BCW6E_ChA_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6E_ChB_D0", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6E_ChB_D1", 0x44, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6F_ChA_D0", 0x55, 0);//PG[b]E7
            physetup_set_msg_block(cfg, pstate, "BCW6F_ChA_D1", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6F_ChB_D0", 0x55, 0);
            physetup_set_msg_block(cfg, pstate, "BCW6F_ChB_D1", 0x55, 0);
        }

        if (cfg->phy_training == DWC_PHY_TRAINING) {
            if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
                physetup_set_msg_block(cfg, pstate, "SequenceCtrl", 0xbe1f, 0);
            } else {
                physetup_set_msg_block(cfg, pstate, "SequenceCtrl", 0x821f, 0);
            }
        } else {
            physetup_set_msg_block(cfg, pstate, "SequenceCtrl", 0x0001, 0);   //Run DevInit only
        }
    } // for num_pstates

#endif  // CINIT_DDR5
#endif // MEMC_DDR5
}


void ddrctl_sw_phyinit_ddr4_config(SubsysHdlr_t *cfg)
{
#ifdef MEMC_DDR4
#ifdef CINIT_DDR4
    uint8_t     pstate;
    uint8_t     channel;
    uint8_t     rcd;
    uint8_t     dis_dynadrtri;
    uint8_t     cs_present;
#ifndef DWC_PHYINIT_RID_GE202008
    uint8_t     is_2t_timing;
#endif
    uint16_t    value;
    uint16_t    disabled_dbyte;
    uint32_t    msgmisc;
    uint32_t    num_dbyte;
    uint32_t    num_active_dbyte_dfi0;
    uint32_t    ddr4_rcd_tstaoff_ps;
    uint32_t    ddr4_rcd_tpdm_ps;
    uint32_t    ddr4_rcd_tpdm_rd_ps;
    char        cmd_str[CINIT_MAX_CMD_STR];

    if ((DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) || (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM)) {
        ddr4_rcd_tstaoff_ps = cfg->timingParams_m[0][0].ddr4_rcd_tstaoff_ps + 2; // Adjust for TxDly
        for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
            snprintf (cmd_str, CINIT_MAX_CMD_STR, "tSTAOFF[%d]", pstate);
            physetup_set_user_input(cfg, cmd_str, ddr4_rcd_tstaoff_ps);
        }

        ddr4_rcd_tpdm_ps = cfg->timingParams_m[0][0].ddr4_rcd_tpdm_ps;
        if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
            physetup_set_user_input(cfg, "tCASL_override", 1);
        }

        for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
            if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
                ddr4_rcd_tpdm_ps = cfg->timingParams_m[0][0].ddr4_rcd_tpdm_ps; // Fixes hif read hash errors + (cfg->spdData_m.tck_ps[pstate]/2);
                // P80001562-131116 - It looks that write data is driven one UI ( half tck） earlier than expected
                if (pstate == 0 && cfg->spdData_m.tck_ps[pstate] <= 1250) {
                    ddr4_rcd_tpdm_ps += DIV_2(cfg->spdData_m.tck_ps[pstate]);
                }
            }
            snprintf (cmd_str, CINIT_MAX_CMD_STR, "tPDM[%d]", pstate);
            physetup_set_user_input(cfg, cmd_str, ddr4_rcd_tpdm_ps);

            if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
                ddr4_rcd_tpdm_rd_ps = cfg->timingParams_m[0][0].ddr4_rcd_tpdm_rd_ps;
                ddr4_rcd_tpdm_rd_ps = ddr4_rcd_tpdm_rd_ps - cfg->timingParams_m[0][0].ddr4_rcd_tpdm_ps; // Adjust for TxDly
                for (pstate = 0; pstate < 4; pstate++) {
                    snprintf (cmd_str, CINIT_MAX_CMD_STR, "tCASL_add[%d][%d]", pstate, pstate);
                    physetup_set_user_input(cfg, cmd_str, ddr4_rcd_tpdm_rd_ps);
                }
            }
        }
    }

    disabled_dbyte = 0;

#ifdef DDRCTL_DDR_DRAM_ECC_WIDTH_GT_0
    if (cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_HALF) {
#if defined(MEMC_DRAM_DATA_WIDTH_GT_63)
        disabled_dbyte = 0xf0;
#elif defined(MEMC_DRAM_DATA_WIDTH_GT_31)
        disabled_dbyte = 0xec;
#else
        disabled_dbyte = 0xfa;
#endif
    } else if (cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_QUARTER) {
#ifdef MEMC_DRAM_DATA_WIDTH_GT_63
        disabled_dbyte = 0xfc;
#else
        disabled_dbyte = 0xee;
#endif
    }
#endif

    //#############################################################################
    //
    // Structure for basic (mandatory) user inputs
    //
    //#############################################################################


    physetup_set_user_input(cfg, "DramType", DWC_DDR4);
    physetup_set_user_input(cfg, "NumPStates", cfg->num_pstates);
    physetup_set_user_input(cfg, "NumRank_dfi0", cfg->spdData_m.num_ranks);
    physetup_set_user_input(cfg, "DisablePmuEcc", 1); //disabled the SRAM ECC feature temporarily
#ifdef DWC_PHYINIT_RID_GE202008
    physetup_set_user_input (cfg, "EnableMAlertAsync",1); //allow async alert
#endif

#ifdef DWC_DDRPHY_DFI1_EXISTS
    physetup_set_user_input(cfg, "Dfi1Exists",1);
#else
    physetup_set_user_input(cfg, "Dfi1Exists", 0);
#endif

    // When MEMC_SIDEBAND_ECC was defined, it indicates the ECC was enabled.
    // ECC byte always use the most significant byte, so both of num_dbyte and enabled_dq should been considered as FBW
    // For HBW/QBW, disabled_dbyte should be used to skip the un-connected dbytes.
    // But, for SNPS_DIMM, an extra define VIRL_DIMM_ECC_MODE_0 will be used to indicate the ECC device won't be used.
    // So, when VIRL_DIMM_ECC_MODE_0 is defined, the num_dbyte shouldn't take into account ECC width.
#ifdef MEMC_SIDEBAND_ECC
    num_dbyte = DIV_8(MEMC_DRAM_TOTAL_DATA_WIDTH);
#else
    num_dbyte = DIV_8(MEMC_DRAM_DATA_WIDTH);
#endif

#ifdef DDRCTL_DDR_DRAM_ECC_WIDTH_GT_0
    num_active_dbyte_dfi0 = num_dbyte;
#else
    if(cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_FULL) {
        num_active_dbyte_dfi0 = num_dbyte;
    } else if(cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_HALF) {
        num_active_dbyte_dfi0 = DIV_2(num_dbyte);
    } else {
        num_active_dbyte_dfi0 = DIV_4(num_dbyte);
    }
#endif

    physetup_set_user_input(cfg, "NumActiveDbyteDfi0", num_active_dbyte_dfi0);

    if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) {
        physetup_set_user_input(cfg, "DimmType_DIMM0", get_dimm_type(cfg));
        physetup_set_user_input(cfg, "DimmType_DIMM1", get_dimm_type(cfg));
    } else {
        physetup_set_user_input(cfg, "DimmType", get_dimm_type(cfg));
    }

    physetup_set_user_input(cfg, "NumAnib", cfg->num_anibs);
    physetup_set_user_input(cfg, "NumDbyte", cfg->num_dbytes);

#ifdef DWC_PHYINIT_RID_GE202201
    physetup_set_user_input(cfg, "DramDataWidth[0]", cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input(cfg, "DramDataWidth[1]", cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input(cfg, "DramDataWidth[2]", cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input(cfg, "DramDataWidth[3]", cfg->spdData_m.sdram_width_bits[0]);
#else
    physetup_set_user_input (cfg, "DramDataWidth", cfg->spdData_m.sdram_width_bits[0]);
#endif

    for (int pstate = 0; pstate < cfg->num_pstates; pstate++) {
        uint32_t freq = CEIL(1000000, cfg->spdData_m.tck_ps[pstate]);
        uint8_t  dfi_freq_ratio;
    
        // For DDR4 only DWC_RATIO_1_2 is supported
        if (ddrctl_sw_get_ratio(cfg, 0) == DWC_RATIO_1_2) {
            dfi_freq_ratio = 1;
        } else {
            dfi_freq_ratio = 2;
        }

        // Memclk frequency in MHz round up to next highest integer
        snprintf (cmd_str, CINIT_MAX_CMD_STR, "DfiFreqRatio[%d]", pstate);
        physetup_set_user_input(cfg, cmd_str, dfi_freq_ratio);

        // Memclk frequency in MHz round up to next highest integer
        snprintf (cmd_str, CINIT_MAX_CMD_STR, "Frequency[%d]", pstate);
        physetup_set_user_input(cfg, cmd_str, freq);
    }

    physetup_set_user_input(cfg, "PllBypass[0]", REGB_DDRC_CH0.mstr0.dll_off_mode);
    physetup_set_user_input(cfg, "PllBypass[1]", 0);  // TODO
    physetup_set_user_input(cfg, "PllBypass[2]", 0);  // TODO
    physetup_set_user_input(cfg, "PllBypass[3]", 0);  // TODO

    if (cfg->spdData_m.num_ranks == 4) {
        cs_present = 0xf;
    } else if (cfg->spdData_m.num_ranks == 2) {
        cs_present = 0x3;
    } else { // 1 rank
        cs_present = 0x1;
    }

    //#############################################################################
    //
    // Structure for advanced (optional) user inputs
    // - if user does not enter a value for these parameters, a PHY recommended or
    //   default value will be used
    //
    //#############################################################################

    for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
        uint16_t wr_preamble;
        uint16_t rd_preamble;

        if((pstate != 0) && (cfg->spdData_m.tck_ps[0] >= 938) ) {
            wr_preamble = 0;
            rd_preamble = 0;
        } else {
            wr_preamble = cfg->memCtrlr_m.ddr4_mr[pstate].mr4.wr_preamble;
            rd_preamble = cfg->memCtrlr_m.ddr4_mr[pstate].mr4.rd_preamble;
        }
        snprintf(cmd_str, CINIT_MAX_CMD_STR, "D4RxPreambleLength[%d]", pstate);
        physetup_set_user_input(cfg, cmd_str, rd_preamble);
        snprintf(cmd_str, CINIT_MAX_CMD_STR, "D4TxPreambleLength[%d]", pstate);
        physetup_set_user_input(cfg, cmd_str, wr_preamble);
    }

    physetup_set_user_input(cfg, "MemAlertEn", 1); // allow dfi_alert_n to be driven to the controller
    // allow async dfi_alert_n if dfi_alert_async_mode=
    physetup_set_user_input(cfg, "EnableMAlertAsync", REGB_DDRC_CH0.crcparctl1.dfi_alert_async_mode);

#ifndef DWC_PHYINIT_RID_GE202008

#ifdef MEMC_CMD_RTN2IDLE
  if( REGB_DDRC_CH0.mstr0.en_2t_timing_mode==1 ) {
      is_2t_timing=1;
  }
#endif

#ifdef MEMC_CMD_RTN2IDLE
  if( REGB_DDRC_CH0.mstr3.geardown_mode == 1 ) {
      is_2t_timing=1;
  }
#endif // MEMC_CMD_RTN2IDLE

    physetup_set_user_input(cfg, "Is2Ttiming[0]", is_2t_timing);
    physetup_set_user_input(cfg, "Is2Ttiming[1]", is_2t_timing);
#ifdef UMCTL2_FREQUENCY_NUM_GT_2
    physetup_set_user_input(cfg, "Is2Ttiming[2]", is_2t_timing);
#endif
#ifdef UMCTL2_FREQUENCY_NUM_GT_3
    physetup_set_user_input(cfg, "Is2Ttiming[3]", is_2t_timing);
#endif
#endif // DWC_PHYINIT_RID_GE202008

    dis_dynadrtri = REGB_DDRC_CH0.dfimisc.dis_dyn_adr_tri;

    physetup_set_user_input(cfg, "DisDynAdrTri[0]", dis_dynadrtri);
    physetup_set_user_input(cfg, "DisDynAdrTri[1]", dis_dynadrtri);
#ifdef UMCTL2_FREQUENCY_NUM_GT_2
    physetup_set_user_input(cfg, "DisDynAdrTri[2]", dis_dynadrtri);
#endif
#ifdef UMCTL2_FREQUENCY_NUM_GT_3
    physetup_set_user_input(cfg, "DisDynAdrTri[3]", dis_dynadrtri);
#endif

    if (cfg->mr7_by_phy) {
        physetup_set_user_input(cfg, "SnpsUmctlOpt", 1);
    }

    //#############################################################################
    //
    // Structure for user input simulation options
    //
    //#############################################################################

    //
    //
    // Setup the message block.
    // MsgMisc[0]: MTESTEnable
    // MsgMisc[1]: SimulationOnlyReset
    // MsgMisc[2]: SimulationOnlyTraining
    // MsgMisc[3]: UseDdr4PerDeviceVrefDq (DDR4 UDIMM/RDIMM only)
    // MsgMisc[4]: Suppress streaming messages
    // MsgMisc[5]: PerByteMaxRdLat
    // MsgMisc[6]: PartialRank
    // MsgMisc[7]: RFU
    //
    msgmisc = 0;
    if (cfg->use_jedec_init == 0) {
        msgmisc |= 1 << 1;
    }
    msgmisc |= 1 << 2;
    if (DDRCTL_GET_DIMM_TYPE(cfg, 0) != DWC_LRDIMM) {
        msgmisc |= 1 << 3;
    }

#ifdef UMCTL2_SHARED_AC
    msgmisc |= 1 << 6;
#endif

    for (pstate = 0; pstate < cfg->num_pstates; pstate++) {
        for (channel = 0; channel < 1; channel++) {  // Hardcode 1 as PHY supports only 1 channel
            physetup_set_msg_block(cfg, pstate, "MsgMisc", msgmisc, TRAIN_2D_DISABLE);
            physetup_set_msg_block(cfg, pstate, "HdtCtrl", cfg->HdtCtrl, TRAIN_2D_DISABLE); // Stage completion
            physetup_set_msg_block(cfg, pstate, "DFIMRLMargin", 1, TRAIN_2D_DISABLE);

            ddrTimingParameters_t *timing = &(cfg->timingParams_m[pstate][0]);
            uint8_t mr0_cl;

            uint32_t addr_mirror;
            if (cfg->spdData_m.addr_mirror) {
                if (cfg->spdData_m.num_ranks == 4) {
                    addr_mirror = 0x4;
                } else if (cfg->spdData_m.num_ranks == 2) {
                    addr_mirror = 0x2;
                } else {
                    addr_mirror = 0;
                }
            } else {
                if (cfg->spdData_m.shared_ac == 1) {
                    addr_mirror = 2;
                } else {
                    addr_mirror = 0;
                }
            }

            mr0_cl = ddrctl_sw_get_ddr4_mr0_cl_code(timing->ddr4_tcl_tck);
            physetup_set_msg_block(cfg, pstate, "CsPresent", cs_present, 0);
            physetup_set_msg_block(cfg, pstate, "DisabledDbyte", disabled_dbyte, TRAIN_2D_DISABLE);
            physetup_set_msg_block(cfg, pstate, "AddrMirror", addr_mirror, 0);
            physetup_set_msg_block(cfg, pstate, "MR0", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR0, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "MR1", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR1, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "MR2", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR2, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "MR3", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR3, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "MR4", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR4, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "MR5", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR5, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "MR6", ddrctl_sw_get_ddr4_mode_reg(DDRCTL_DDR4_MR6, pstate, channel), 0);
            physetup_set_msg_block(cfg, pstate, "ALT_CAS_L", (SNPS_GET_BIT(mr0_cl, 4) << 12)      |
                                                                (SNPS_GETBITMASK(mr0_cl, 3, 1) << 4) |
                                                                (SNPS_GET_BIT(mr0_cl, 0) << 2) | 0x1, 0);
            //ALT_WCAS_L[0] = 1: use value in ALT_WCAS_L,depends on MR4[12]
            physetup_set_msg_block(cfg, pstate, "ALT_WCAS_L",
                    ((SNPS_GETBITMASK(cfg->memCtrlr_m.ddr4_mr[pstate].mr2.cwl, 2, 0) << 3) | 1), 0);

            // Only 1 registered clock drivers supported (when using RDIMMs)
            rcd = 0;
            if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_RDIMM) {
                // DDR4 RCD0
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "CsPresentD%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, cs_present, 0);

                // Inversion Enabled, Weak drive disabled, A/B outputs enabled
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC00_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC00, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC01_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC01, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC08_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC08, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC0A_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC0A, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC0D_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC0D, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC0E_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC0E, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC0F_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC0F, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0RC3x_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_rcd_cw(cfg, DDRCTL_DDR4_F0RC3X, pstate), 0);
            }

            if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "BC0A_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_bcw_4b(cfg, DDRCTL_DDR4_BC0A, pstate), 0);
                snprintf(cmd_str, CINIT_MAX_CMD_STR, "F0BC6x_D%d", rcd);
                physetup_set_msg_block(cfg, pstate, cmd_str, ddrctl_sw_get_ddr4_bcw_8b(cfg, DDRCTL_DDR4_B0BC6x, pstate), 0);
            }

            if (cfg->phy_training == DWC_PHY_TRAINING) {
                if (DDRCTL_GET_DIMM_TYPE(cfg, 0) == DWC_LRDIMM) {
                    physetup_set_msg_block(cfg, pstate, "SequenceCtrl", 0x3f1f, 0);
                } else {
                    physetup_set_msg_block(cfg, pstate, "SequenceCtrl", 0x31f, 0);
                }
            } else {
                physetup_set_msg_block(cfg, pstate, "SequenceCtrl", 0x0001, 0);   //Run DevInit only
            }
        } // for num_dch
    } // for num_pstates
#endif  // CINIT_DDR4
#endif // MEMC_DDR4
}

/** @brief Function to call function need when configuring PHYINIT.
 * The follow steps are taken:
 * - calculate some local variables to map to PHYINT requirements.
 * - Setup userInputBasic
 * - Setup userInputAdvanced
 * - Setup userInputSim
 */
void dwc_cinit_phyinit_setuserinput(SubsysHdlr_t *cfg)
{
    hdlr = cfg;
#ifdef DWC_PHYINIT_RID_GE202102
    physetup_set_user_input (cfg, "pubRev", DWC_DDRPHY_PUB_RID);
#endif

#ifdef CINIT_DDR4
    ddrctl_sw_phyinit_ddr4_config(cfg);
#endif  // CINIT_DDR4
#ifdef CINIT_DDR5
    ddrctl_sw_phyinit_ddr5_config(cfg);
#endif  // CINIT_DDR4

}



#endif // DDRCTL_DDR
#endif // DDR5_PHY
