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

#include "mode_regs/ddr4/ddrctl_sw_ddr4_mode_regs_macros.h"
#include "mode_regs/ddr4/ddrctl_sw_ddr4_mode_regs.h"
#include "dwc_ddrctl_cinit_util.h"
#include "cinit_status.h"
#include "dwc_cinit_log.h"

#ifdef DDRCTL_DDR

uint8_t ddrctl_sw_get_ddr4_mr0_cl_code(uint8_t cas_latency)
{
    uint8_t mr0_cl = 0;

    switch (cas_latency) {
        case 9:
            mr0_cl = 0;
            break;
        case 10:
            mr0_cl = 1;
            break;
        case 11:
            mr0_cl = 2;
            break;
        case 12:
            mr0_cl = 3;
            break;
        case 13:
            mr0_cl = 4;
            break;
        case 14:
            mr0_cl = 5;
            break;
        case 15:
            mr0_cl = 6;
            break;
        case 16:
            mr0_cl = 7;
            break;
        case 17:
            mr0_cl = 13;
            break;
        case 18:
            mr0_cl = 8;
            break;
        case 19:
            mr0_cl = 14;
            break;
        case 20:
            mr0_cl = 9;
            break;
        case 21:
            mr0_cl = 15;
            break;
        case 22:
            mr0_cl = 10;
            break;
        case 23:
            mr0_cl = 12;
            break;
        case 24:
            mr0_cl = 11;
            break;
        case  25 :
            mr0_cl = 16;
            break;
        case 26:
            mr0_cl = 17;
            break;
        case 27 :
            mr0_cl = 18;//only 3DS available
            break;
        case 28:
            mr0_cl = 19;
            break;
        case 30:
            mr0_cl = 21;
            break;
        case 32:
            mr0_cl = 23;
            break;
        default:
            mr0_cl = 255;
            break;
    }

    return mr0_cl;
}

/**
 * @brief helper method to return 8 bit MR data value from struct
 */
uint16_t ddrctl_sw_get_ddr4_mode_reg(ddrctl_ddr4_mr_t mr, uint8_t pstate, uint8_t channel)
{
    uint16_t mr_value = 0;
    uint8_t is_geardown = 0;

#ifdef MEMC_CMD_RTN2IDLE
  if (REGB_DDRC_CH0.mstr3.geardown_mode == 1) {
      is_geardown = 1;
  }
#endif // MEMC_CMD_RTN2IDLE

    switch(mr) {
        case DDRCTL_DDR4_MR0:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr0.mr;
            break;
        case DDRCTL_DDR4_MR1:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr0.emr;
            break;
        case DDRCTL_DDR4_MR2:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr1.emr2;
            break;
        case DDRCTL_DDR4_MR3:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr1.emr3;
            break;
        case DDRCTL_DDR4_MR4:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr2.mr4;
            break;
        case DDRCTL_DDR4_MR5:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr2.mr5;
            // Geardown entry happens after SRX and it should be done with CA parity off
            // So if geardown is enabled, CA parity must be disabled before SRE
            if (is_geardown == 1) {
                SNPS_WRITE_EXPLICIT_FIELD(mr_value, 0, 0x7, 0); //C/A Parity Latency Mode
            }
            break;
        case DDRCTL_DDR4_MR6:
            mr_value = g_ctrl_regs.REGB[pstate].FREQ_CH[channel].initmr3.mr6;
            break;
        default:
            SNPS_ERROR("MR %d not supported", mr);
            dwc_ddrctl_cinit_exit(1);
            break;
    }

    return mr_value;
}

#endif // DDRCTL_DDR
