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

#include "mode_regs/ddr5/ddrctl_sw_ddr5_mode_regs.h"
#include "ddrctl_sw_ddr5_mode_regs_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "cinit_status.h"
#include "dwc_cinit_log.h"

#ifdef DDRCTL_DDR

/**
 * @brief helper method to return 8 bit MR data value from struct to
 * be used in MRW.
*/
uint8_t ddrctl_sw_get_ddr5_mode_reg(SubsysHdlr_t *cfg, uint8_t pstate, uint8_t mr_num)
{
    ddr5_mode_registers_t *mode_regs;
    uint8_t mr_value = 0;

    mode_regs = &(cfg->memCtrlr_m.ddr5_mr[pstate]);

    //internal write timing must be enabled, Reference: dwc_ddr54_phy_training_firmware_application_note_2.50a, Table 3-6 DDR5 MR and CW Restrictions - Required Settings  
    mode_regs->mr2.internal_wr_timing = 0x1; 

    switch(mr_num) {
        case 0:
            SNPS_WRITE_FIELD(mr_value, DDR5_MR0_BURST_LENGTH, mode_regs->mr0.burst_length);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR0_CAS_LATENCY,  mode_regs->mr0.cl);
            break;
        case 2:
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_READ_PREAMBLE_EN,       mode_regs->mr2.rd_preamble_enable);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_WRITE_LEVELING,         mode_regs->mr2.wr_leveling);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_2N_MODE,                mode_regs->mr2.ddr5_2n_mode);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_MAX_POWER_SAVING_MODE,  mode_regs->mr2.mpsm);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_CS_ASSERT_DURATION,     mode_regs->mr2.cs_assertion_duration);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_DEV_15_MPSM,            mode_regs->mr2.dev15_mpsm);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR2_INTERNAL_WRITE_TIMMING, mode_regs->mr2.internal_wr_timing);
            break;
        case 4:
            SNPS_WRITE_FIELD(mr_value, DDR5_MR4_REFRESH_RATE,      mode_regs->mr4.refresh_rate);
            SNPS_WRITE_FIELD(mr_value, DDR5_MR4_REFRESH_TRFC_MODE, mode_regs->mr4.refresh_trfc_mode);
            break;
        case 5:
            //SNPS_WRITE_FIELD(mr_value, ,);
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr5.data_output_disable,1,0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr5.pull_up_output_drv_impedance,2,1) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr5.tdqs_enable,1,4) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr5.dm_enable,1,5) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr5.pull_down_output_drv_impedance,2,6);
            break;
        case 6:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr6.wr_recovery,4,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr6.trtp,4,4);
            break;
        case 8:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr8.rd_preamble,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr8.wr_preamble,2,3) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr8.rd_postamble,1,6) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr8.wr_postamble,1,7);
            break;
        case 13:
            mr_value = mode_regs->mr13.tccd_l & 0xf;
            break;
        case 15:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr15.etc,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr15.auto_ecs_in_selfref,3,1);
            break;
        case 34:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr34.rtt_park,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr34.rtt_wr,3,3);
            break;
        case 35:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr35.rtt_nom_wr,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr35.rtt_nom_rd,3,3);
            break;
        case 37:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr37.odtlon_wr_offset,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr37.odtloff_wr_offset,3,3);
            break;
        case 38:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr38.odtlon_wr_nt_offset,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr38.odtloff_wr_nt_offset,3,3);
            break;
        case 39:
            mr_value = DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr39.odtlon_rd_nt_offset,3,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr39.odtloff_rd_nt_offset,3,3);
            break;
        case 40:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr40.rd_dqs_offset,3,0);
            break;
        case 45:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr45.osc_run_time,8,0);
            break;
        case 50:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr50.rd_crc_enable,1,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr50.wr_crc_enable_lower_nibble,1,1) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr50.wr_crc_enable_upper_nibble,1,2) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr50.wr_crc_error_status,1,3) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr50.wr_crc_auto_disable_enable,1,4) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr50.wr_crc_auto_disable_status,1,5);
            break;
        case 51:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr51.wr_crc_auto_disable_thre,7,0);
            break;
        case 52:
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr52.wr_crc_auto_disable_window,7,0);
            break;
        case 58:
            // MR58 this is defined as per rank only taking rank 0 here
            mr_value=DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr58[0].rfm_required,1,0) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr58[0].raa_initial_management_threshold,4,1) |
                DWC_DDRCTL_SETREGBITFIELDSHIFT(mode_regs->mr58[0].raa_maximum_management_threshold,3,5);
            break;
        default:
            SNPS_ERROR("MR 0x%0x not supported", mr_num);
            dwc_ddrctl_cinit_exit(1);
            break;
    }

    return mr_value;
}

#endif // DDRCTL_DDR
