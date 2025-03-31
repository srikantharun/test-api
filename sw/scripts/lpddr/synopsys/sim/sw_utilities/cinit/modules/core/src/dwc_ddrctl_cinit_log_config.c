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


#include "dwc_ddrctl_cinit_log_config.h"
#include "dwc_ddrctl_cinit_types_str.h"
#include "jedec/ddr4/cinit_ddr4_speed_bins_strings.h"
#include "jedec/ddr5/cinit_ddr5_speed_bins_strings.h"
#include "jedec/ddr5/cinit_ddr5_types.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "cinit_status.h"
#include "ddrctl_cinit_ime.h"


#define DDRCTL_CINIT_LOG_ALIGN          24
#define DDRCTL_CINIT_LOG_ALIGN_LEVEL     4


#define SNPS_LOG_CFG(var_str, var_print, ...) \
    do { \
        SNPS_LOG("%-*s: " var_print, DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)

#define SNPS_LOG_PSTATE_CFG(pstate, var_str, var_print, ...) \
    do { \
        SNPS_LOG("[pState %u] %-*s: " var_print, pstate, \
                  DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)


#define SNPS_LOG_CHANNEL_CFG(channel, var_str, var_print, ...) \
    do { \
        SNPS_LOG("[Ch %u] %-*s: " var_print, channel, \
                   DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)

#define SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, var_str, var_print, ...) \
    do { \
        SNPS_LOG("[Ch %u] [Rank %u] %-*s: " var_print, channel, rank, \
                  DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)

#define SNPS_LOG_PSTATE_RANK_CFG(pstate, rank, var_str, var_print, ...) \
    do { \
        SNPS_LOG("[pState %u] [Rank %u] %-*s: " var_print, pstate, rank, \
                  DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)

#define SNPS_LOG_DEVICE_CFG(dev, var_str, var_print, ...) \
    do { \
        SNPS_LOG("[Dev %u] %-*s: " var_print, dev, \
                  DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)


#define SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, var_str, var_print, ...) \
    do { \
        SNPS_LOG("[pState %u] [Ch %u] %-*s: " var_print, pstate, channel, \
                 DDRCTL_CINIT_LOG_ALIGN, var_str, __VA_ARGS__); \
    } while (0)


/** @brief utility function to print an initial debug message. */
void _log_cinit_version(void)
{
    uint32_t version_major;
    uint32_t version_minor;

    version_major = ddr_cinit_get_major_version();
    version_major = SWAP_UINT32(version_major);

    version_minor = ddr_cinit_get_minor_version();
    version_minor = SWAP_UINT32(version_minor);

    SNPS_LOG_CFG("CINIT version", "%.4s_%.2s", (char *)&version_major,
                                               &((char *)&version_minor)[2]);
}


void _log_hardware_cfg(SubsysHdlr_t *cinit_cfg)
{
    uint32_t ver_number;
    uint32_t ver_type;

    ver_number = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DDRCTL_VER_NUMBER);
    ver_number = SWAP_UINT32(ver_number);
    ver_type   = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DDRCTL_VER_TYPE);
    ver_type   = SWAP_UINT32(ver_type);

    SNPS_LOG_CFG("Controller version", "%.3s_%.3s", (char *)&ver_number, (char *)&ver_type);
#ifdef DDRCTL_SINGLE_INST_DUALCH
    SNPS_LOG_CFG("Ctlr[0] Base Addr ", "0x%016llx", cinit_cfg->ddrctl_base_addr[0]);
    SNPS_LOG_CFG("Ctlr[1] Base Addr ", "0x%016llx", cinit_cfg->ddrctl_base_addr[1]);
#elif defined(LPDDR_2MC1PHY)
    SNPS_LOG_CFG("Ctlr[0] Base Addr ", "0x%016llx", cinit_cfg->ddrctl_base_addr[0]);
    SNPS_LOG_CFG("Ctlr[1] Base Addr ", "0x%016llx", cinit_cfg->ddrctl_base_addr[1]);
#else
    SNPS_LOG_CFG("Ctlr Base Addr ", "0x%016llx", cinit_cfg->ddrctl_base_addr[0]);
#endif
    SNPS_LOG_CFG("PHY Type", "%s (%d)", ddrctl_sw_get_phy_type_str(cinit_cfg->ddrPhyType_m),
                                     cinit_cfg->ddrPhyType_m);
    SNPS_LOG_CFG("Phy Train mode", "%s (%d)", ddrctl_sw_get_phy_train_str(cinit_cfg->phy_training),
                                           cinit_cfg->phy_training);
}


void _log_dfy_timing_cfg(SubsysHdlr_t *cinit_cfg)
{
    phy_timing_params_t *timing;
    mctl_pre_cfg        *pre_cfg;
    uint8_t             pstate;
    uint8_t             channel;
    uint8_t             device;

    pre_cfg = &(cinit_cfg->memCtrlr_m.pre_cfg);
    timing  = &(cinit_cfg->phy_timing_params);

    SNPS_INFO("########################################");
    SNPS_INFO("            DFY parameters");
    SNPS_LOG_CFG("Pipe write",      "%d", timing->pipe_dfi_wr);
    SNPS_LOG_CFG("Pipe read",       "%d", timing->pipe_dfi_rd);
    SNPS_LOG_CFG("Pipe misc",       "%d", timing->pipe_dfi_misc);
    SNPS_LOG_CFG("TLP resp",        "%d", timing->dfi_tlp_resp);
    SNPS_LOG_CFG("TPhy write data", "%d", timing->dfi_tphy_wrdata);
    SNPS_LOG_CFG("tCtrlUp max",     "%d", timing->dfi_t_ctrlup_max);
    SNPS_LOG_CFG("tCtrlUp min",     "%d", timing->dfi_t_ctrlup_min);
    SNPS_LOG_CFG("tCtrl delay",     "%d", timing->dfi_t_ctrl_delay);
    SNPS_LOG_CFG("TLP data wakeup", "%d", timing->dfi_tlp_data_wakeup);

#ifdef DDRCTL_DDR
    SNPS_LOG_CFG("t2n mode delay", "%d", timing->dfi_t_2n_mode_delay);
#endif
    SNPS_INFO("");
    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_dram_clk_disable", "%u",
                               pre_cfg->dfi_t_dram_clk_disable[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_dram_clk_enable", "%u",
                               pre_cfg->dfi_t_dram_clk_enable[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "phy_wrlat", "%u",
                               pre_cfg->dfi_tphy_wrlat[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rddata_en", "%u",
                               pre_cfg->dfi_t_rddata_en[pstate][channel]);
            SNPS_INFO("########################################");
        }
    }
}

void _log_memory_cfg(SubsysHdlr_t *cinit_cfg)
{
    ddrSpdData_t       *memcfg;
    dwc_sdram_protocol  protocol;
    uint8_t             channel;
    uint8_t             device;

    memcfg = &(cinit_cfg->spdData_m);
    protocol = memcfg->sdram_protocol;

    SNPS_LOG_CFG("Protocol", "%s (%d)", ddrctl_sw_get_protocol_str(protocol), protocol);

    switch (protocol) {
#ifdef DDRCTL_LPDDR
        case DWC_LPDDR4:
            if (memcfg->use_lpddr4x) {
                SNPS_LOG_CFG("Protocol variant", "%s", "LPDDR4x");
            }
            SNPS_LOG_CFG("Data rate", "%s",
                         ddrctl_sw_get_lpddr4_data_rate_str(memcfg->lpddr4_data_rate));
            break;
        case DWC_LPDDR5:
            if (memcfg->use_lpddr5x) {
                SNPS_LOG_CFG("Protocol variant", "%s", "LPDDR5x");
            }
            SNPS_LOG_CFG("Data rate", "%s",
                         ddrctl_sw_get_lpddr5_data_rate_str(memcfg->lpddr5_data_rate));
            break;
#endif /* DDRCTL_LPDDR */
#ifdef DDRCTL_DDR
        case DWC_DDR4:
            SNPS_LOG_CFG("Speed Bin", "%s",
                         ddrctl_sw_get_ddr4_speed_bin_str(memcfg->ddr4_sg));
            break;
        case DWC_DDR5:
            SNPS_LOG_CFG("Jedec", "%s",
                         ddrctl_cinit_get_ddr5_version_str(memcfg->ddr5_jedec_spec));
            break;
#endif /* DDRCTL_DDR */
        default:
            break;
    }

    SNPS_LOG_CFG("PStates", "%d", cinit_cfg->num_pstates);
    SNPS_LOG_CFG("Address Maps", "%d", cinit_cfg->num_amap);
    SNPS_LOG_CFG("Number of Channels", "%d", cinit_cfg->num_dch);
    SNPS_LOG_CFG("Module", "%s", ddrctl_sw_get_module_str(memcfg->module_type));
    SNPS_LOG_CFG("Ranks", "%d", memcfg->num_ranks);
    SNPS_LOG_CFG("Number of DIMMs", "%d", memcfg->num_dimm);
    SNPS_LOG_CFG("Ranks per DIMM", "%d", memcfg->num_ranks_per_dimm);

    for (device = 0; device < DWC_DDRCTL_DEV_CFG_NUM; device++) {
#ifdef DDRCTL_DDR
        if (DWC_DDR5 == protocol) {
            SNPS_LOG_DEVICE_CFG(device, "Speed Bin", "%s",
                        ddrctl_cinit_get_ddr5_speed_bin_str(memcfg->ddr5_speed_bin[device]));
        }
#endif /* DDRCTL_DDR */
        SNPS_LOG_DEVICE_CFG(device, "Capacity", "%u mbits",
                            memcfg->sdram_capacity_mbits[device]);
        SNPS_LOG_DEVICE_CFG(device, "3DS CIDs", "%s",
                            ddrctl_sw_get_cid_str(memcfg->cid_width[device]));
        SNPS_LOG_DEVICE_CFG(device, "Row address", "%d",
                            memcfg->dram_raw[device]);
        SNPS_LOG_DEVICE_CFG(device, "Column address", "%d",
                            memcfg->dram_caw[device]);
        SNPS_LOG_DEVICE_CFG(device, "Bank address", "%d",
                            memcfg->dram_baw[device]);
        SNPS_LOG_DEVICE_CFG(device, "Bank group address", "%d",
                            memcfg->dram_bgw[device]);
        SNPS_LOG_DEVICE_CFG(device, "SDRAM width", "%d",
                            memcfg->sdram_width_bits[device]);
    }
    SNPS_LOG_CFG("SDRAM Bus Width", "%s",
                 ddrctl_sw_get_sdram_bus_width_str(cinit_cfg->memCtrlr_m.sdram_bus_width));
    SNPS_LOG_CFG("Additive Latency", "%d bits", memcfg->tAL);
    SNPS_LOG_CFG("Read DBI Add Latency", "%d bits", memcfg->tAL_RDBI);

#ifdef DDRCTL_DDR
    SNPS_LOG_CFG("capar_retry_window_internal_delay_extra", "0x%.8x", 
                 cinit_cfg->capar_retry_window_internal_delay_extra);
#endif /* DDRCTL_DDR */
#ifdef DDRCTL_LPDDR
    if (DWC_LPDDR4 == protocol) {
        SNPS_LOG_CFG("Scaling Level", "%u", memcfg->lpddr4_scl);
    }
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
    if (DWC_DDR4 == protocol) {
        SNPS_LOG_CFG("Address Mirror", "%u", memcfg->addr_mirror);
        SNPS_LOG_CFG("Use tCWL_x lower set", "%u bits", memcfg->use_ddr4_tcwl_1st_set);
    }

    if (DWC_DDR5 == protocol) {
        SNPS_LOG_CFG("tRx_DQS2DQ", "%u ps", memcfg->trx_dqs2dq);
        SNPS_LOG_CFG("Data width per channel", "%s",
                     ddrctl_sw_get_dimm_data_width_str(memcfg->ddr5_dimm_ch_arch));
    }
#endif
}


void _log_ddr4_timing_cfg(SubsysHdlr_t *cinit_cfg)
{
#ifndef DDRCTL_DDR
    CINIT_UNUSED(cinit_cfg);
#else
    uint8_t                 pstate;
    uint8_t                 channel;
    ddrTimingParameters_t  *timing;
    mctl_pre_cfg    *pre_cfg;

    pre_cfg = &(cinit_cfg->memCtrlr_m.pre_cfg);

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_INFO("########################################");
        SNPS_LOG_PSTATE_CFG(pstate, "tCK(avg)", "%u ps", cinit_cfg->spdData_m.tck_ps[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "Frequency ratio", "%s",
                            ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));
        SNPS_LOG_PSTATE_CFG(pstate, "CAS Latency(CL)", "%u", pre_cfg->cl[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "cl_dbi", "%u", pre_cfg->cl_dbi[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "cwl_x", "%u", pre_cfg->cwl_x[pstate]);
        for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
            timing = &cinit_cfg->timingParams_m[pstate][channel];

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "Burst Lengh", "%u",
                                        timing->burst_length);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRCD", "%u",
                                            pre_cfg->t_rcd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRC", "%u",
                                        pre_cfg->t_rc[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRAS(min)", "%u ps",
                                        pre_cfg->t_ras_min[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRAS(max)", "%u ps",
                                        pre_cfg->t_ras_max[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tFAW", "%u",
                                        pre_cfg->tfaw[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRRD", "%u",
                                        pre_cfg->t_rrd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRRD_s", "%u",
                                        timing->trrd_s_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tXSDLL", "%u tCKs",
                                        timing->ddr4_txsdll_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "RCD tPDM_RD", "%u ps",
                                        timing->ddr4_rcd_tpdm_rd_ps);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "RCD tPDM_WR", "%u ps",
                                        timing->ddr4_rcd_tpdm_wr_ps);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd", "%u",
                                        pre_cfg->wr2rd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rd2wr", "%u",
                                        pre_cfg->rd2wr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tMPX_LH", "%u",
                                        pre_cfg->t_mpx_lh[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tMPX_S", "%u",
                                        pre_cfg->t_mpx_s[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tCKMPE", "%u",
                                        pre_cfg->t_ckmpe[pstate][channel]);
        }
    }

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_LOG_PSTATE_CFG(pstate, "MR0_WR_RECOVERY", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr0.wr_recovery);

        SNPS_LOG_PSTATE_CFG(pstate, "MR0_DLL_RESET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr0.dll_reset);
        SNPS_LOG_PSTATE_CFG(pstate, "MR0_CL", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr0.cl);
        SNPS_LOG_PSTATE_CFG(pstate, "MR0_BURST_TYPE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr0.burst_type);
        SNPS_LOG_PSTATE_CFG(pstate, "MR0_BURST_LENGTH", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr0.burst_length);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_RTT_NOM", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr1.rtt_nom);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_WR_LEVELING_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr1.wr_leveling_enable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_AL", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr1.al);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_OUTPUT_DRIVER_IMPEDANCE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr1.output_driver_impedance);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_DLL_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr1.dll_enable);

        SNPS_LOG_PSTATE_CFG(pstate, "MR2_WRITE_CRC", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr2.write_crc);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_RTT_WR", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr2.rtt_wr);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_AUTO_SELF_REF", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr2.auto_self_ref);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_CWL", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr2.cwl);

        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WCL", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr3.wcl);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_GEARDOWN", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr3.geardown);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_MPR_OP", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr3.mpr_op);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_MPR_PS", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr3.mpr_ps);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_FINE_GRANULARITY_REFRESH", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr3.fine_granularity_refresh);

        SNPS_LOG_PSTATE_CFG(pstate, "MR4_WR_PREAMBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr4.wr_preamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR4_RD_PREAMBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr4.rd_preamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR4_SELFREF_ABORT", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr4.selfref_abort);
        SNPS_LOG_PSTATE_CFG(pstate, "MR4_CAL", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr4.cal);
        SNPS_LOG_PSTATE_CFG(pstate, "MR4_REFRESH_MODE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr4.refresh_mode);
        SNPS_LOG_PSTATE_CFG(pstate, "MR4_REFRESH_RANGE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr4.refresh_range);


        SNPS_LOG_PSTATE_CFG(pstate, "MR5_READ_DBI", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.read_dbi);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_WRITE_DBI", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.write_dbi);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_DATA_MASK", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.data_mask);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_CA_PARITY_PERSISTENT", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.ca_parity_persistent);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_RTT_PARK", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.rtt_park);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_DIS_ODT_INPUT_BUF_IN_PD", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.dis_odt_input_buf_in_pd);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_PARITY_LATENCY_MODE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr5.parity_latency_mode);

        SNPS_LOG_PSTATE_CFG(pstate, "MR6_TCCD_L", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr4_mr[pstate].mr6.tccd_l);
    }

    SNPS_LOG_CFG("RC0F Latency Adder nladd to all DRAM cmd", " 0x%.8x",
            cinit_cfg->ddr4_cw.rc0f.latency_adder_nladd_to_all_dram_cmd);

#endif /* DDRCTL_DDR */
}


void _log_ddr5_timing_cfg(SubsysHdlr_t *cinit_cfg)
{
#ifndef DDRCTL_DDR
    CINIT_UNUSED(cinit_cfg);
#else
    uint8_t                pstate;
    uint8_t                channel;
    uint8_t                rank;
    uint32_t               base_freq;
    dwc_ddr5_speed_grade_t speed_grade;
    mctl_pre_cfg          *pre_cfg;
    ddrTimingParameters_t *timing;

    pre_cfg = &(cinit_cfg->memCtrlr_m.pre_cfg);

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_INFO("########################################");

        speed_grade = cinit_ddr5_get_speedgrade_from_tck_avg_min(cinit_cfg->spdData_m.tck_ps[pstate]);
        base_freq   = cinit_ddr5_get_speedgrade_base_frequency(speed_grade);
        SNPS_LOG_PSTATE_CFG(pstate, "tCK(min)", "%u ps (%d MT/s)",
                            cinit_cfg->spdData_m.tck_ps[pstate], base_freq);
        SNPS_LOG_PSTATE_CFG(pstate, "Frequency ratio", "%s",
                            ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));

        SNPS_LOG_PSTATE_CFG(pstate, "CAS Latency(CL)", "%d", pre_cfg->cl[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "CAS Write Latency(CWL)", "%d", pre_cfg->cwl_x[pstate]);

        for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
            timing  = &(cinit_cfg->timingParams_m[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "Burst Lengh", "%u",
                                        timing->burst_length);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRAS(min)", "%u ps",
                                        pre_cfg->t_ras_min[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tRAS(max)", "%u ps",
                                        pre_cfg->t_ras_max[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_faw", "%u",
                                        pre_cfg->tfaw[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rc", "%u",
                                        pre_cfg->t_rc[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rcd", "%u",
                                         pre_cfg->t_rcd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rrd", "%u",
                                        pre_cfg->t_rrd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rrd_s", "%u",
                                        timing->trrd_s_tck);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "write_latency", "%u",
                                        pre_cfg->cwl_x[pstate]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "read_latency", "%u",
                                        pre_cfg->cl[pstate]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "Read CRC Latency Adder", "%u",
                                        timing->ddr5_read_crc_latency_adder);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ccd", "%u",
                                        pre_cfg->t_ccd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ccd_w", "%u",
                                        pre_cfg->t_ccd_w[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ccd_w_s", "%u",
                                        timing->ddr5_tccd_s_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ccd_w2", "%u",
                                        pre_cfg->t_ccd_w2[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ccd_r", "%u",
                                        timing->ddr5_tccd_l_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ccd_r_s", "%u",
                                        timing->ddr5_tccd_s_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rd2wr_l", "%u",
                                        pre_cfg->rd2wr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_wr2rd_l", "%u",
                                        pre_cfg->wr2rd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_wr2rd_s", "%u",
                                        pre_cfg->wr2rd_s[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_wr2rd_dpr", "%u",
                                        pre_cfg->t_wr2rd_dpr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rd2wr_dpr", "%u",
                                        pre_cfg->t_rd2wr_dpr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_rp", "%u",
                                        pre_cfg->t_rp[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_ppd", "%u",
                                        timing->ddr5_tppd_tck);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_pd", "%u",
                                        pre_cfg->t_pd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_mr", "%u",
                                        pre_cfg->t_mr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_mpsmx", "%u",
                                        pre_cfg->t_mpsmx[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_mpdpxact", "%u",
                                        pre_cfg->t_mpdpxact[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_pda_latch", "%u",
                                        pre_cfg->t_pda_latch[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_pda_delay", "%u",
                                        pre_cfg->t_pda_delay[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_pda_dqs_delay", "%u",
                                        pre_cfg->t_pda_dqs_delay[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_pda_s", "%u",
                                        pre_cfg->t_pda_s[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_pda_h", "%u",
                                        pre_cfg->t_pda_h[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_cpded", "%u",
                                        pre_cfg->t_cpded[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_casrx", "%u",
                                        pre_cfg->t_casrx[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_csh_srexit", "%u",
                                        pre_cfg->t_csh_srexit[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_csl_srexit", "%u",
                                        pre_cfg->t_csl_srexit[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_mpc_cs", "%u",
                                        pre_cfg->t_mpc_cs[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_mpc_setup", "%u",
                                        pre_cfg->t_mpc_setup[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "t_mpc_delay", "%u",
                                        pre_cfg->t_mpc_delay[pstate][channel]);
        }
    }

    for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
        SNPS_LOG_CHANNEL_CFG(channel, "base_timer_interval", "%u us",
                             cinit_cfg->ddr5_pasdu_en.base_timer_interval_us[channel]);
        SNPS_LOG_CHANNEL_CFG(channel, "all_rank_zqcal_en", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_en.all_rank_zqcal_en[channel]);
        SNPS_LOG_CHANNEL_CFG(channel, "all_rank_zqcal_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.all_rank_zqcal_thres[channel]);
        SNPS_LOG_CHANNEL_CFG(channel, "all_rank_zqlat_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.all_rank_zqlat_thres[channel]);
        SNPS_LOG_CHANNEL_CFG(channel, "ctlupd_en", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_en.ctlupd_en[channel]);
        SNPS_LOG_CHANNEL_CFG(channel, "ctlupd_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.ctlupd_thres[channel]);
        for (rank = 0; rank < cinit_cfg->spdData_m.num_ranks; rank++) {
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "tcr_dqsosc_en", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_en.tcr_dqsosc_en[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "dqsosc_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.dqsosc_thres[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "tcr_mrr_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.tcr_mrr_thres[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "per_rank_zqcal_en", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_en.per_rank_zqcal_en[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "per_rank_zqcal_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.per_rank_zqcal_thres[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "per_rank_zqlat_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.per_rank_zqlat_thres[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "per_rank_zqlat_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.per_rank_zqlat_thres[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "per_rank_ecs_en", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_en.per_rank_ecs_en[channel][rank]);
            SNPS_LOG_CHANNEL_RANK_CFG(channel, rank, "ecs_thres", "0x%.8x",
                            cinit_cfg->ddr5_pasdu_thres.ecs_thres[channel][rank]);
        }
    }
    SNPS_LOG_CFG("trx_dqs2dq", "%u", cinit_cfg->spdData_m.trx_dqs2dq);

    SNPS_LOG_CFG("RW00 SDR mode", " 0x%.8x", cinit_cfg->ddr5_cw.rw00.sdr_mode);
    SNPS_LOG_CFG("RW11 Latency Adder nladd to all DRAM cmd", " 0x%.8x",
                 cinit_cfg->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd);


    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tCCD_w_offset", " 0x%.8x",
                               cinit_cfg->ddr5_interamble_tccd_offset.t_ccd_w_offset[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tCCD_r_offset", " 0x%.8x",
                               cinit_cfg->ddr5_interamble_tccd_offset.t_ccd_r_offset[pstate][channel]);
        }
    }

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_LOG_PSTATE_CFG(pstate, "MR0 CL", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr0.cl);
        SNPS_LOG_PSTATE_CFG(pstate, "MR0 BURST_LENGTH", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr0.burst_length);

        SNPS_LOG_PSTATE_CFG(pstate, "MR2_RD_PREAMBLE_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.rd_preamble_enable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_WR_LEVELING", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.wr_leveling);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_DDR5_2N_MODE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.ddr5_2n_mode);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_MPSM", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.mpsm);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_CS_ASSERTION_DURATION", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.cs_assertion_duration);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_DEV15_MPSM", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.dev15_mpsm);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_INTERNAL_WR_TIMING", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr2.internal_wr_timing);

        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WR_LEVELING_INTERNAL_LOWER_BYTE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr3.wr_leveling_internal_lower_byte);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WR_LEVELING_INTERNAL_UPPER_BYTE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr3.wr_leveling_internal_upper_byte);

        SNPS_LOG_PSTATE_CFG(pstate, "MR4_REFRESH_TRFC_MODE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr4.refresh_trfc_mode);
        SNPS_LOG_PSTATE_CFG(pstate, "MR4_REFRESH_RATE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr4.refresh_rate);

        SNPS_LOG_PSTATE_CFG(pstate, "MR5_DATA_OUTPUT_DISABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr5.data_output_disable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_PULL_UP_OUTPUT_DRV_IMPEDANCE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr5.pull_up_output_drv_impedance);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_TDQS_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr5.tdqs_enable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_DM_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr5.dm_enable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR5_PULL_DOWN_OUTPUT_DRV_IMPEDANCE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr5.pull_down_output_drv_impedance);

        SNPS_LOG_PSTATE_CFG(pstate, "MR6_TRTP", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr6.trtp);
        SNPS_LOG_PSTATE_CFG(pstate, "MR6_WR_RECOVERY", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr6.wr_recovery);


        SNPS_LOG_PSTATE_CFG(pstate, "MR8_RD_PREAMBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr8.rd_preamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR8_WR_PREAMBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr8.wr_preamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR8_RD_POSTAMBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr8.rd_postamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR8_WR_POSTAMBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr8.wr_postamble);

        SNPS_LOG_PSTATE_CFG(pstate, "MR13_TCCD_L", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr13.tccd_l);

        SNPS_LOG_PSTATE_CFG(pstate, "MR34_RTT_PARK", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr34.rtt_park);
        SNPS_LOG_PSTATE_CFG(pstate, "MR34_RTT_WR", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr34.rtt_wr);

        SNPS_LOG_PSTATE_CFG(pstate, "MR35_RTT_NOM_WR", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr35.rtt_nom_wr);
        SNPS_LOG_PSTATE_CFG(pstate, "MR35_RTT_NOM_RD", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr35.rtt_nom_rd);

        SNPS_LOG_PSTATE_CFG(pstate, "MR37_ODTLON_WR_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr37.odtlon_wr_offset);
        SNPS_LOG_PSTATE_CFG(pstate, "MR37_ODTLOFF_WR_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr37.odtloff_wr_offset);

        SNPS_LOG_PSTATE_CFG(pstate, "MR38_ODTLON_WR_NT_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr38.odtlon_wr_nt_offset);
        SNPS_LOG_PSTATE_CFG(pstate, "MR38_ODTLOFF_WR_NT_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr38.odtloff_wr_nt_offset);

        SNPS_LOG_PSTATE_CFG(pstate, "MR39_ODTLON_RD_NT_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr39.odtlon_rd_nt_offset);
        SNPS_LOG_PSTATE_CFG(pstate, "MR39_ODTLOFF_RD_NT_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr39.odtloff_rd_nt_offset);

        SNPS_LOG_PSTATE_CFG(pstate, "MR40_RD_DQS_OFFSET", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr40.rd_dqs_offset);

        SNPS_LOG_PSTATE_CFG(pstate, "MR45_OSC_RUN_TIME", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr45.osc_run_time);

        SNPS_LOG_PSTATE_CFG(pstate, "MR50_RD_CRC_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr50.rd_crc_enable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR50_WR_CRC_ENABLE_LOWER_NIBBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr50.wr_crc_enable_lower_nibble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR50_WR_CRC_ENABLE_UPPER_NIBBLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr50.wr_crc_enable_upper_nibble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR50_WR_CRC_ERROR_STATUS", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr50.wr_crc_error_status);
        SNPS_LOG_PSTATE_CFG(pstate, "MR50_WR_CRC_AUTO_DISABLE_ENABLE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr50.wr_crc_auto_disable_enable);
        SNPS_LOG_PSTATE_CFG(pstate, "MR50_WR_CRC_AUTO_DISABLE_STATUS", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr50.wr_crc_auto_disable_status);

        SNPS_LOG_PSTATE_CFG(pstate, "MR51_WR_CRC_AUTO_DISABLE_THRE", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr51.wr_crc_auto_disable_thre);

        SNPS_LOG_PSTATE_CFG(pstate, "MR52_WR_CRC_AUTO_DISABLE_WINDOW", "0x%.8x",
                            cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr52.wr_crc_auto_disable_window);

        for (rank = 0; rank < cinit_cfg->spdData_m.num_ranks; rank++) {
            SNPS_LOG_PSTATE_RANK_CFG(pstate, rank, "MR58_RFM_REQUIRED", "0x%.8x",
                    cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr58[rank].rfm_required);
            SNPS_LOG_PSTATE_RANK_CFG(pstate, rank, "MR58_RAA_INITIAL_MANAGEMENT_THRESHOLD", "0x%.8x",
                    cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr58[rank].raa_initial_management_threshold);
            SNPS_LOG_PSTATE_RANK_CFG(pstate, rank, "MR58_RAA_MAXIMUM_MANAGEMENT_THRESHOLD", "0x%.8x",
                    cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr58[rank].raa_maximum_management_threshold);

            SNPS_LOG_PSTATE_RANK_CFG(pstate, rank, "MR59_RAA_COUNTER_DECR_PER_REF_CMD", "0x%.8x",
                    cinit_cfg->memCtrlr_m.ddr5_mr[pstate].mr59[rank].raa_counter_decr_per_ref_cmd);
        }
    }
#endif /* DDRCTL_DDR */
}


void _log_lpddr4_timing_cfg(SubsysHdlr_t *cinit_cfg)
{
#ifndef DDRCTL_LPDDR
    CINIT_UNUSED(cinit_cfg);
#else
    uint8_t                pstate;
    uint8_t                channel;
    mctl_pre_cfg          *pre_cfg;
    ddrTimingParameters_t *timing;
    lpddr4_mode_registers_t *lpddr4_mr;

    pre_cfg = &(cinit_cfg->memCtrlr_m.pre_cfg);

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_LOG_PSTATE_CFG(pstate, "tCK(avg)", "%u ps", cinit_cfg->spdData_m.tck_ps[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "Frequency ratio", "%s", 
                     ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));
        for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
            timing  = &(cinit_cfg->timingParams_m[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "trfcab", "%u",
                                        timing->lpddr4_trfcab);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tpbr2pbr", "%u",
                                        timing->lpddr4_tpbr2pbr);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wl", "%u",
                                        pre_cfg->wl[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rl", "%u",
                                        pre_cfg->rl[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd", "%u",
                                        pre_cfg->wr2rd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd_s", "%u",
                                         pre_cfg->wr2rd_s[pstate][channel]);
        }
    }

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        lpddr4_mr = &(cinit_cfg->memCtrlr_m.lpddr4_mr[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_RD_POSTAMBLE", "0x%.8x", lpddr4_mr->mr1.rd_postamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_WR_RECOVERY",  "0x%.8x", lpddr4_mr->mr1.wr_recovery);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_RD_PREAMBLE",  "0x%.8x", lpddr4_mr->mr1.rd_preamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_WR_PREAMBLE",  "0x%.8x", lpddr4_mr->mr1.wr_preamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_BURST_LENGTH", "0x%.8x", lpddr4_mr->mr1.burst_length);

        SNPS_LOG_PSTATE_CFG(pstate, "MR2_WLS", "0x%.8x", lpddr4_mr->mr2.wls);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_RL_WL", "0x%.8x", lpddr4_mr->mr2.rl_wl);

        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WRITE_DBI", "0x%.8x", lpddr4_mr->mr3.write_dbi);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_READ_DBI", "0x%.8x", lpddr4_mr->mr3.read_dbi);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_PDDS", "0x%.8x", lpddr4_mr->mr3.pdds);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_PPRP", "0x%.8x", lpddr4_mr->mr3.pprp);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WR_POSTAMBLE", "0x%.8x", lpddr4_mr->mr3.wr_postamble);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_PU_CAL", "0x%.8x", lpddr4_mr->mr3.pu_cal);

        SNPS_LOG_PSTATE_CFG(pstate, "MR11_CA_ODT", "0x%.8x", lpddr4_mr->mr11.ca_odt);
        SNPS_LOG_PSTATE_CFG(pstate, "MR11_DQ_ODT", "0x%.8x", lpddr4_mr->mr11.dq_odt);

        SNPS_LOG_PSTATE_CFG(pstate, "MR12_VR_CA", "0x%.8x", lpddr4_mr->mr12.vr_ca);
        SNPS_LOG_PSTATE_CFG(pstate, "MR12_VREF_CA", "0x%.8x", lpddr4_mr->mr12.vref_ca);

        SNPS_LOG_PSTATE_CFG(pstate, "MR13_FSP_OP", "0x%.8x", lpddr4_mr->mr13.fsp_op);
        SNPS_LOG_PSTATE_CFG(pstate, "MR13_FSP_WR", "0x%.8x", lpddr4_mr->mr13.fsp_wr);
        SNPS_LOG_PSTATE_CFG(pstate, "MR13_DMD", "0x%.8x", lpddr4_mr->mr13.dmd);

        SNPS_LOG_PSTATE_CFG(pstate, "MR14_VR_DQ", "0x%.8x", lpddr4_mr->mr14.vr_dq);
        SNPS_LOG_PSTATE_CFG(pstate, "MR14_VREF_DQ", "0x%.8x", lpddr4_mr->mr14.vref_dq);

        SNPS_LOG_PSTATE_CFG(pstate, "MR22_ODTD", "0x%.8x", lpddr4_mr->mr22.odtd);
        SNPS_LOG_PSTATE_CFG(pstate, "MR22_ODTD_CA", "0x%.8x", lpddr4_mr->mr22.odtd_ca);
        SNPS_LOG_PSTATE_CFG(pstate, "MR22_ODTD_CS", "0x%.8x", lpddr4_mr->mr22.odtd_cs);
        SNPS_LOG_PSTATE_CFG(pstate, "MR22_ODTD_CK", "0x%.8x", lpddr4_mr->mr22.odtd_ck);
        SNPS_LOG_PSTATE_CFG(pstate, "MR22_SOC_ODT", "0x%.8x", lpddr4_mr->mr22.soc_odt);
    }
#endif    /* DDRCTL_LPDDR */
}


void _log_lpddr5_timing_cfg(SubsysHdlr_t *cinit_cfg)
{
#ifndef DDRCTL_LPDDR
    CINIT_UNUSED(cinit_cfg);
#else
    uint8_t                  pstate;
    uint8_t                  channel;
    mctl_pre_cfg            *pre_cfg;
    ddrTimingParameters_t   *timing;
    ddrSpdData_t            *memcfg;
    lpddr5_mode_registers_t *lpddr5_mr;

    memcfg = &(cinit_cfg->spdData_m);
    pre_cfg = &(cinit_cfg->memCtrlr_m.pre_cfg);

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_LOG_PSTATE_CFG(pstate, "tCK(avg)", "%u ps", cinit_cfg->spdData_m.tck_ps[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "WCK:CK ratio", "%s",
                   ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));
        SNPS_LOG_PSTATE_CFG(pstate, "Bank/BankGroup Org", "%s",
                   ddrctl_sw_get_lpddr5_bk_bg_str(memcfg->lpddr5_bk_bg_org[pstate]));

        for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
            timing  = &(cinit_cfg->timingParams_m[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wl", "%u",
                                        pre_cfg->wl[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rl", "%u",
                                        pre_cfg->rl[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd", "%u",
                                        pre_cfg->wr2rd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd_s", "%u",
                                        pre_cfg->wr2rd_s[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wra2pre", "%u",
                                        pre_cfg->wra2pre[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rda2pre", "%u",
                                        pre_cfg->rda2pre[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tccd_s", "%u tCk",
                                        timing->lpddr5_tccd_s_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "tccd_l", "%u tCk",
                                        timing->lpddr5_tccd_l_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "twtr_s", "%u ps",
                                        timing->lpddr5_twtr_s_ps);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "twtr_l", "%u ps",
                                        timing->lpddr5_twtr_l_ps);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "bl_n_min", "%u tCk",
                                        timing->lpddr5_bl_n_min_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "bl_n_max", "%u tCk",
                                        timing->lpddr5_bl_n_max_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rl", "%u tCk", timing->lpddr5_rl_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wl", "%u tCk", timing->lpddr5_wl_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wckpre_static", "%u tCk",
                                        timing->lpddr5_wckpre_static_tck);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "twck_pst_wck", "%u",
                                        timing->lpddr5_twck_pst_wck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wckenl_rd", "%u tCk",
                                        timing->lpddr5_wckenl_rd_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wckenl_wr", "%u tCk",
                                        timing->lpddr5_wckenl_wr_tck);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wckenl_fs", "%u tCk",
                                        timing->lpddr5_wckenl_fs_tck);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "trfcab", "%u ps", timing->lpddr5_trfcab_ps);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "trfcpb", "%u ps", timing->lpddr5_trfcpb_ps);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "nrbtp", "%u", timing->lpddr5_nrbtp);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "twr", "%u ps", timing->lpddr5_twr_ps);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_en_rd", "%u",
                               pre_cfg->dfi_twck_en_rd[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_en_wr", "%u",
                               pre_cfg->dfi_twck_en_wr[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_en_fs", "%u",
                               pre_cfg->dfi_twck_en_fs[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_dis", "%u",
                               pre_cfg->dfi_twck_dis[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_fast_toggle", "%u",
                               pre_cfg->dfi_twck_fast_toggle[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_toggle", "%u",
                               pre_cfg->dfi_twck_toggle[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_toggle_cs", "%u",
                               pre_cfg->dfi_twck_toggle_cs[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dfi_twck_toggle_post", "%u",
                               pre_cfg->dfi_twck_toggle_post[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "max_wr_sync", "%u",
                                        pre_cfg->max_wr_sync[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "max_rd_sync", "%u",
                                        pre_cfg->max_rd_sync[pstate][channel]);
#ifdef MEMC_NUM_RANKS_GT_1
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wck_on", "%u",
                                        QDYN.wck_on[pstate]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "dq_odt", "%u",
                                        cinit_cfg->memCtrlr_m.lpddr5_mr[pstate].mr11.dq_odt);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "nt_odt", "%u",
                                        cinit_cfg->memCtrlr_m.lpddr5_mr[pstate].mr11.nt_odt);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "nt_dq_odt", "%u",
                               cinit_cfg->memCtrlr_m.lpddr5_mr[pstate].mr41.nt_dq_odt);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "odtloff", "%u",
                                        pre_cfg->odtloff[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "odtlon", "%u",
                                        pre_cfg->odtlon[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rd2wr_dr", "%u",
                               pre_cfg->rd2wr_dr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rd2wr_dr_odt", "%u",
                               pre_cfg->rd2wr_dr_odt[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rd2wr_dr_wck_on", "%u",
                               pre_cfg->rd2wr_dr_wck_on[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "rd2wr_dr_wck_on_odt", "%u",
                               pre_cfg->rd2wr_dr_wck_on_odt[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd_dr", "%u",
                               pre_cfg->wr2rd_dr[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd_dr_odt", "%u",
                               pre_cfg->wr2rd_dr_odt[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd_dr_wck_on", "%u",
                               pre_cfg->wr2rd_dr_wck_on[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "wr2rd_dr_wck_on_odt", "%u",
                               pre_cfg->wr2rd_dr_wck_on_odt[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_rd_gap", "%u",
                               pre_cfg->diff_rank_rd_gap[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_rd_gap_odt", "%u",
                               pre_cfg->diff_rank_rd_gap_odt[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_rd_gap_wck_on", "%u",
                               pre_cfg->diff_rank_rd_gap_wck_on[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_rd_gap_wck_on_odt", "%u",
                               pre_cfg->diff_rank_rd_gap_wck_on_odt[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_rd_gap_wck_on_dq_odt_nt_odt", "%u",
                               pre_cfg->diff_rank_rd_gap_wck_on_dq_odt_nt_odt[pstate][channel]);

            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_wr_gap", "%u",
                               pre_cfg->diff_rank_wr_gap[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_wr_gap_odt", "%u",
                               pre_cfg->diff_rank_wr_gap_odt[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_wr_gap_wck_on", "%u",
                               pre_cfg->diff_rank_wr_gap_wck_on[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_wr_gap_wck_on_odt", "%u",
                               pre_cfg->diff_rank_wr_gap_wck_on_odt[pstate][channel]);
            SNPS_LOG_PSTATE_CHANNEL_CFG(pstate, channel, "diff_rank_wr_gap_wck_on_dq_odt_nt_odt", "%u",
                               pre_cfg->diff_rank_wr_gap_wck_on_dq_odt_nt_odt[pstate][channel]);
#endif    /* MEMC_NUM_RANKS_GT_1 */
        }
    }

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        lpddr5_mr = &(cinit_cfg->memCtrlr_m.lpddr5_mr[pstate]);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_WRITE_LATENCY", "0x%.8x", lpddr5_mr->mr1.write_latency);
        SNPS_LOG_PSTATE_CFG(pstate, "MR1_CK_MODE", "0x%.8x", lpddr5_mr->mr1.ck_mode);

        SNPS_LOG_PSTATE_CFG(pstate, "MR2_NWR", "0x%.8x", lpddr5_mr->mr2.nwr);
        SNPS_LOG_PSTATE_CFG(pstate, "MR2_RL_NRTP", "0x%.8x", lpddr5_mr->mr2.rl_nrtp);

        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WRITE_DBI", "0x%.8x", lpddr5_mr->mr3.write_dbi);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_READ_DBI", "0x%.8x", lpddr5_mr->mr3.read_dbi);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_WLS", "0x%.8x", lpddr5_mr->mr3.wls);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_BK_BG_ORG", "0x%.8x", lpddr5_mr->mr3.bk_bg_org);
        SNPS_LOG_PSTATE_CFG(pstate, "MR3_PDDS", "0x%.8x", lpddr5_mr->mr3.pdds);

        SNPS_LOG_PSTATE_CFG(pstate, "MR10_RDQS_PST_MODE", "0x%.8x", lpddr5_mr->mr10.rdqs_pst_mode);
        SNPS_LOG_PSTATE_CFG(pstate, "MR10_RDQS_PST", "0x%.8x", lpddr5_mr->mr10.rdqs_pst);
        SNPS_LOG_PSTATE_CFG(pstate, "MR10_RDQS_PRE_2", "0x%.8x", lpddr5_mr->mr10.rdqs_pre_2);
        SNPS_LOG_PSTATE_CFG(pstate, "MR10_WCK_PST", "0x%.8x", lpddr5_mr->mr10.wck_pst);
        SNPS_LOG_PSTATE_CFG(pstate, "MR10_RDQS_PRE", "0x%.8x", lpddr5_mr->mr10.rdqs_pre);

        SNPS_LOG_PSTATE_CFG(pstate, "MR11_CS_ODT_OP", "0x%.8x", lpddr5_mr->mr11.cs_odt_op);
        SNPS_LOG_PSTATE_CFG(pstate, "MR11_CA_ODT", "0x%.8x", lpddr5_mr->mr11.ca_odt);
        SNPS_LOG_PSTATE_CFG(pstate, "MR11_NT_ODT", "0x%.8x", lpddr5_mr->mr11.nt_odt);
        SNPS_LOG_PSTATE_CFG(pstate, "MR11_DQ_ODT", "0x%.8x", lpddr5_mr->mr11.dq_odt);

        SNPS_LOG_PSTATE_CFG(pstate, "MR12_VBS", "0x%.8x", lpddr5_mr->mr12.vbs);
        SNPS_LOG_PSTATE_CFG(pstate, "MR12_VREF_CA", "0x%.8x", lpddr5_mr->mr12.vref_ca);

        SNPS_LOG_PSTATE_CFG(pstate, "MR13_DUAL_VDD2", "0x%.8x", lpddr5_mr->mr13.dual_vdd2);
        SNPS_LOG_PSTATE_CFG(pstate, "MR13_DMD", "0x%.8x", lpddr5_mr->mr13.dmd);
        SNPS_LOG_PSTATE_CFG(pstate, "MR13_VRO", "0x%.8x", lpddr5_mr->mr13.vro);
        SNPS_LOG_PSTATE_CFG(pstate, "MR13_THERMAL_OFFSET", "0x%.8x", lpddr5_mr->mr13.thermal_offset);

        SNPS_LOG_PSTATE_CFG(pstate, "MR14_VDLC", "0x%.8x", lpddr5_mr->mr14.vdlc);
        SNPS_LOG_PSTATE_CFG(pstate, "MR14_VREF_DQ", "0x%.8x", lpddr5_mr->mr14.vref_dq);

        SNPS_LOG_PSTATE_CFG(pstate, "MR15_VREF_DQ", "0x%.8x", lpddr5_mr->mr15.vref_dq);

        SNPS_LOG_PSTATE_CFG(pstate, "MR16_CBT", "0x%.8x", lpddr5_mr->mr16.cbt);
        SNPS_LOG_PSTATE_CFG(pstate, "MR16_VRCG", "0x%.8x", lpddr5_mr->mr16.vrcg);
        SNPS_LOG_PSTATE_CFG(pstate, "MR16_FSP_OP", "0x%.8x", lpddr5_mr->mr16.fsp_op);
        SNPS_LOG_PSTATE_CFG(pstate, "MR16_FSP_WR", "0x%.8x", lpddr5_mr->mr16.fsp_wr);

        SNPS_LOG_PSTATE_CFG(pstate, "MR17_ODTD", "0x%.8x", lpddr5_mr->mr17.odtd);
        SNPS_LOG_PSTATE_CFG(pstate, "MR17_ODTD_CA", "0x%.8x", lpddr5_mr->mr17.odtd_ca);
        SNPS_LOG_PSTATE_CFG(pstate, "MR17_ODTD_CS", "0x%.8x", lpddr5_mr->mr17.odtd_cs);
        SNPS_LOG_PSTATE_CFG(pstate, "MR17_ODTD_CK", "0x%.8x", lpddr5_mr->mr17.odtd_ck);
        SNPS_LOG_PSTATE_CFG(pstate, "MR17_SOC_ODT", "0x%.8x", lpddr5_mr->mr17.soc_odt);

        SNPS_LOG_PSTATE_CFG(pstate, "MR18_CKR", "0x%.8x", lpddr5_mr->mr18.ckr);
        SNPS_LOG_PSTATE_CFG(pstate, "MR18_WCK2CK_LEVELING", "0x%.8x",
                            lpddr5_mr->mr18.wck2ck_leveling);
        SNPS_LOG_PSTATE_CFG(pstate, "MR18_WCK_ON", "0x%.8x", lpddr5_mr->mr18.wck_on);
        SNPS_LOG_PSTATE_CFG(pstate, "MR18_WCK_FM", "0x%.8x", lpddr5_mr->mr18.wck_fm);
        SNPS_LOG_PSTATE_CFG(pstate, "MR18_WCK_ODT", "0x%.8x", lpddr5_mr->mr18.wck_odt);

        SNPS_LOG_PSTATE_CFG(pstate, "MR19_DVFSQ", "0x%.8x", lpddr5_mr->mr19.dvfsq);
        SNPS_LOG_PSTATE_CFG(pstate, "MR19_DVFSC", "0x%.8x", lpddr5_mr->mr19.dvfsc);

        SNPS_LOG_PSTATE_CFG(pstate, "MR20_WCK_MODE", "0x%.8x", lpddr5_mr->mr20.wck_mode);
        SNPS_LOG_PSTATE_CFG(pstate, "MR20_RDQS", "0x%.8x", lpddr5_mr->mr20.rdqs);

        SNPS_LOG_PSTATE_CFG(pstate, "MR21_DCFE", "0x%.8x", lpddr5_mr->mr21.dcfe);
        SNPS_LOG_PSTATE_CFG(pstate, "MR21_WXFS", "0x%.8x", lpddr5_mr->mr21.wxfs);

        SNPS_LOG_PSTATE_CFG(pstate, "MR22_WECC", "0x%.8x", lpddr5_mr->mr22.wecc);
        SNPS_LOG_PSTATE_CFG(pstate, "MR22_RECC", "0x%.8x", lpddr5_mr->mr22.recc);

        SNPS_LOG_PSTATE_CFG(pstate, "MR23_PASR_MASK", "0x%.8x", lpddr5_mr->mr23.pasr_mask);

        SNPS_LOG_PSTATE_CFG(pstate, "MR24_DFEQL", "0x%.8x", lpddr5_mr->mr24.dfeql);
        SNPS_LOG_PSTATE_CFG(pstate, "MR24_DFEQU", "0x%.8x", lpddr5_mr->mr24.dfequ);

        SNPS_LOG_PSTATE_CFG(pstate, "MR25_CK_BUS_TERM", "0x%.8x", lpddr5_mr->mr25.ck_bus_term);
        SNPS_LOG_PSTATE_CFG(pstate, "MR25_CA_BUS_TERM", "0x%.8x", lpddr5_mr->mr25.ca_bus_term);
        SNPS_LOG_PSTATE_CFG(pstate, "MR25_PARC", "0x%.8x", lpddr5_mr->mr25.parc);

        SNPS_LOG_PSTATE_CFG(pstate, "MR28_ZQ_INT", "0x%.8x", lpddr5_mr->mr28.zq_int);
        SNPS_LOG_PSTATE_CFG(pstate, "MR28_ZQ_STOP", "0x%.8x", lpddr5_mr->mr28.zq_stop);
        SNPS_LOG_PSTATE_CFG(pstate, "MR28_ZQ_RESET", "0x%.8x", lpddr5_mr->mr28.zq_reset);

        SNPS_LOG_PSTATE_CFG(pstate, "MR37_WCK2DQI_RUNTIME", "0x%.8x", lpddr5_mr->mr37.wck2dqi_runtime);

        SNPS_LOG_PSTATE_CFG(pstate, "MR40_WCK2DQO_RUNTIME", "0x%.8x", lpddr5_mr->mr40.wck2dqo_runtime);
    }
#endif    /* DDRCTL_LPDDR */
}


/** @brief method to print debug information to cinit log file .
 */
void ddrctl_cinit_log_config(SubsysHdlr_t *cinit_cfg)
{
    ddrSpdData_t    *memcfg;

    memcfg = &(cinit_cfg->spdData_m);

    _log_cinit_version();

    SNPS_INFO("########################################");

    _log_hardware_cfg(cinit_cfg);

    SNPS_INFO("########################################");

    _log_memory_cfg(cinit_cfg);

    if (DWC_DDR4 == memcfg->sdram_protocol) {
        _log_ddr4_timing_cfg(cinit_cfg);
    }

    if (DWC_DDR5 == memcfg->sdram_protocol) {
        _log_ddr5_timing_cfg(cinit_cfg);
    }

    if (DWC_LPDDR4 == memcfg->sdram_protocol) {
        _log_lpddr4_timing_cfg(cinit_cfg);
    }

    if (DWC_LPDDR5 == memcfg->sdram_protocol) {
        _log_lpddr5_timing_cfg(cinit_cfg);
    }

    _log_dfy_timing_cfg(cinit_cfg);

    ddrctl_cinit_ime_cfg_log(cinit_cfg);
}
