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


#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrphy_VDEFINES.h"

#ifdef DDRCTL_DDR
uint32_t get_ddr5_dqsosc_runtime(uint32_t t_osc);

/** @brief method to apply user options from defconfig file to CINIT structures.
 * Some mode registers are automatically set so that they match the controller
 * settings
 * */
void dwc_ddrctl_cinit_ddr_setuserinput(void)
{
    // apply values from customer defconfig file
    // defines are loaded from .autoconf.h

    dwc_cinit_set_operational_clk_period(hdlr);
    // apply static settings some manually
#ifdef DDR5_PHY
    CFG->num_dbytes = DWC_DDR5PHY_NUM_DBYTES;
    CFG->dfi1_exists = 1;
#else
    CFG->num_anibs = DWC_DDRPHY_NUM_ANIBS;
    CFG->num_dbytes = DWC_DDRPHY_NUM_DBYTES;
#endif
    CFG->use_jedec_init = 0;
    CFG->HdtCtrl = 0xC8;
    SPD.trx_dqs2dq = 114; // min legal ps value
#ifdef DWC_DDRPHY_DFI1_EXISTS
    CFG->dfi1_exists = 1;
#endif
    // automatically set MR registers that MUST be align to controller
    // settings
    for (uint32_t pp = 0; pp < CFG->num_pstates; pp++) {
        DDR5_MR[pp].mr0.burst_length = STATIC.burstchop;
        DDR5_MR[pp].mr4.refresh_trfc_mode = QDYN.fgr_mode;
        DDR5_MR[pp].mr50.wr_crc_enable_lower_nibble = QDYN.wr_crc_enable;
        DDR5_MR[pp].mr50.wr_crc_enable_upper_nibble = QDYN.wr_crc_enable;
        DDR5_MR[pp].mr50.rd_crc_enable = QDYN.rd_crc_enable;
        if ( DDR5_MR[pp].mr45.osc_run_time == 0 ) {
            // cannot use 0 for DqsOscRunTimeSel, PhyInit will throw fatal error.
            DDR5_MR[pp].mr45.osc_run_time = get_ddr5_dqsosc_runtime(QDYN.t_oscs);
            SNPS_WARN("DDR5 MR45.DQS Interval Timer Run Time cannot be 0. Overriding to %d",
                      DDR5_MR[pp].mr45.osc_run_time);
        }
        // DDR4 mode registers
        DDR4_MR[pp].mr0.burst_length = STATIC.burstchop;
        DDR4_MR[pp].mr1.dll_enable = 1;
        DDR4_MR[pp].mr2.write_crc = QDYN.wr_crc_enable;
        DDR4_MR[pp].mr3.geardown = QDYN.geardown_mode[0];
        DDR4_MR[pp].mr3.fine_granularity_refresh = QDYN.fgr_mode;
        DDR4_MR[pp].mr4.wr_preamble = QDYN.ddr4_wr_preamble[pp][0];
        DDR4_MR[pp].mr5.read_dbi = QDYN.rd_dbi_en[0];
        DDR4_MR[pp].mr5.write_dbi = QDYN.wr_dbi_en[0];
        DDR4_MR[pp].mr5.data_mask = QDYN.dm_en[0];
        DDR4_MR[pp].mr5.ca_parity_persistent = 1;
    }
    DDR5_CW.rw00.ca_rate = DDR5_MR[0].mr2.ddr5_2n_mode;

#ifndef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH 
    // if HW is single channel make sure dual_channel_en defaults to 0
    STATIC.dual_channel_en = 0;
    CFG->num_dch = 1;
#endif // UMCTL2_DUAL_CHANNEL
}
/** @brief based on t_osc setting return encoded vale for MR45.osc_run_time */
uint32_t get_ddr5_dqsosc_runtime(uint32_t t_osc) {
    uint32_t dqsosc_runtime;
    // encode to MR45
    if(t_osc < (64*16)) {
      dqsosc_runtime = t_osc/16;
    }
    else if ((t_osc > 1024) && (t_osc <=2047)) {
      dqsosc_runtime = 0x3f;
    }
    else if((t_osc >= 2048) && (t_osc <=4095)) {
      dqsosc_runtime = 0x40;
    }
    else if((t_osc >= 4096) && (t_osc <= 8191)) {
     dqsosc_runtime = 0x80;
    }
    else
      dqsosc_runtime = 0xc0;
    SNPS_LOG("t_osc = %u setting dqsosc_runtime = %u", t_osc, dqsosc_runtime);
    return dqsosc_runtime;
}
#endif
