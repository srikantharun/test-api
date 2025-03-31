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


#include "dwc_ddrctl_phy_training_common.h"
#include "dwc_ddrctl_cinit_common_sequences.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "cinit_status.h"
#include "physetup.h"
#include "phy/ddr54/sinit_ddrphy54_regmap.h"


/**
 * @brief Set the phy wrdata delay
 */
bool dwc_ddrctl_phy_train_wrdata_delay(void)
{
    uint8_t     i;
    uint8_t     pstate;
    uint8_t     dbyte;
    uint8_t     dq_nibble;
    uint32_t    txdqsdly_addr;
    uint8_t     t_wrdata_delay;
    uint16_t    dly_64_prec;
    uint16_t    txdqsdly_data;
    uint16_t    txdqsdly_coarse;
    uint16_t    txdqsdly_fine;
    uint16_t    txdqsdly_mask;
    uint16_t    txdqsdly;
    uint16_t    txdqsdly_remainder;
    uint16_t    txdqsdly_max = 0;
    uint32_t    dfitmg1;
    uint32_t    tmgcfg_freq_ratio;
    uint8_t     channel;
    uint8_t     num_channels;

    num_channels = cinit_get_num_channels_enable();

    // - tphy_wrdata_delay
    // - DDR5: tctrl_delay + (13 + 1 + BL/2) + Trained_TxDqsDly - M2N
    // - DDR4: tctrl_delay + ( 5 + 1 + BL/2) + Trained_TxDqsDly

    tmgcfg_freq_ratio = SNPS_READ_FIELD(dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(0, 0) + TMGCFG),
                                        TMGCFG_FREQUENCY_RATIO);

    dly_64_prec = SNPS_READ_FIELD(physetup_io_read16(TIMINGMODECNTRL), TIMINGMODECNTRL_DLY64PREC);

    for (pstate = 0; pstate <= CFG->num_pstates; pstate++) {
	#ifdef DWC_LPDDR5XPHY_NUM_DBYTES
        for (dbyte = 0; dbyte < DWC_LPDDR5XPHY_NUM_DBYTES; dbyte++) {
	#elif DWC_DDR5PHY_NUM_DBYTES_PER_CHANNEL
        for (dbyte = 0; dbyte < DWC_DDR5PHY_NUM_DBYTES_PER_CHANNEL; dbyte++) {
	#else
        for (dbyte = 0; dbyte < DWC_DDRPHY_NUM_DBYTES; dbyte++) {
	#endif
            for (dq_nibble = 0; dq_nibble <= 1; dq_nibble++) {
                //  TxDqsDlyTg0_uY_pX (for X = 0; X <= 3)(for Y = 0; Y <= 1)
                //             (0x10000+(j<<12))+0xd0+(X*0x100000)+(Y*0x100)
                // x -> pstate
                // y -> dq_nibble
                // j -> dbyte (instance number)
                txdqsdly_addr = TXDQSDLYTG0_UY_PX(pstate, dbyte, dq_nibble);

                // i -> register index (TxDqsDlyTg0 -> TxDqsDlyTg3)
                for (i = 0; i < 4; i++) {
                    txdqsdly_data = physetup_io_read16(txdqsdly_addr + i);
                    txdqsdly_coarse = SNPS_READ_FIELD(txdqsdly_data, TXDQSDLYTG0_COARSE);

                    txdqsdly_mask = (0 == dly_64_prec) ? TXDQSDLYTG0_FINE_32_MASK : TXDQSDLYTG0_FINE_64_MASK;
                    txdqsdly_fine   = SNPS_READ_EXPLICIT_FIELD(txdqsdly_data, TXDQSDLYTG0_FINE_BIT_OFFSET, txdqsdly_mask);

                    //Divide by 2 in (1:2 Mode, tmgcfg_freq_ratio = 0) and round it up
                    //Divide by 4 in (1:4 Mode, tmgcfg_freq_ratio = 0) and round it up
                    if (0 == tmgcfg_freq_ratio) {
                        txdqsdly = DIV_2(txdqsdly_coarse);
                        txdqsdly_remainder = txdqsdly_coarse % 2;
                    } else {
                        txdqsdly = DIV_4(txdqsdly_coarse);
                        txdqsdly_remainder = txdqsdly_coarse % 4;
                    }

                    if ((txdqsdly_remainder != 0) || (txdqsdly_fine > 0)) {
                        txdqsdly += 1;
                    }
                    txdqsdly_max = max(txdqsdly, txdqsdly_max);
                }
            }
        }
    }

    for(channel = 0; channel < num_channels; channel++) {

        dfitmg1 = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(0, channel) + DFITMG1);

        t_wrdata_delay = SNPS_READ_FIELD(dfitmg1, DFITMG1_DFI_T_WRDATA_DELAY);
        SNPS_LOG("[DFI Write Data Timing]Controller delay: ch %d ctrl_t_wrdata_delay=%d", channel, t_wrdata_delay);
        SNPS_LOG("[DFI Write Data Timing]PHY trained delay: ch %d TxDqsDly=%d", channel, txdqsdly_max);

        t_wrdata_delay = t_wrdata_delay + txdqsdly_max;

        SNPS_WRITE_FIELD(dfitmg1, DFITMG1_DFI_T_WRDATA_DELAY, t_wrdata_delay);

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
        }

        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, channel) + DFITMG1, dfitmg1);

        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_LOG("Error in seq_post_qdyn_write");
            return false;
        }

        SNPS_LOG("[DFI Write Data Timing]Expected delay: ch %d t_wrdata_delay=%d", channel, t_wrdata_delay);
    }

    return true;
}


#ifdef DDRCTL_DDR
#ifndef DDR5_PHY

/**
 * @brief Set the phy Address Command delay
 *
 * @note: Needs to be reimplemented for LPDDR, since the algorithm and reg_map is different
 */
bool dwc_ddrctl_phy_train_ctrl_delay(void)
{
    uint8_t     pstate;
    uint8_t     anibs;
    uint16_t    addr_cmd_delay_coarse;
    uint16_t    addr_cmd_delay_fine;
    uint16_t    addr_cmd_delay_remainder;
    uint16_t    addr_cmd_delay_max = 0;
    uint16_t    addr_cmd_delay_calc;
    uint32_t    up_addr_cmd_delay_addr;
    uint32_t    lu_addr_cmd_delay_addr;
    uint16_t    up_addr_cmd_delay_data;
    uint16_t    lu_addr_cmd_delay_data;
    uint32_t    dfitmg0;
    uint32_t    dfi_t_ctrl_delay;
    uint32_t    tmgcfg_freq_ratio;
    uint8_t     channel;
    uint8_t     num_channels;

    num_channels = cinit_get_num_channels_enable();

    tmgcfg_freq_ratio = SNPS_READ_FIELD(dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(0, 0) + TMGCFG),
                                        TMGCFG_FREQUENCY_RATIO);

    for (pstate = 0; pstate <= CFG->num_pstates; pstate++) {
        for (anibs = 0; anibs < DWC_DDRPHY_NUM_ANIBS; anibs++) {
            up_addr_cmd_delay_addr = ATUDLY_PX(pstate, anibs);
            up_addr_cmd_delay_data = physetup_io_read16(up_addr_cmd_delay_addr);
            SNPS_LOG("[Upper Addr/Cmd signals delay 0x%02x",up_addr_cmd_delay_data);

            lu_addr_cmd_delay_addr = ATXDLY_PX(pstate, anibs);
            lu_addr_cmd_delay_data = physetup_io_read16(lu_addr_cmd_delay_addr);
            SNPS_LOG("[Lower Addr/Cmd signals delay 0x%02x",lu_addr_cmd_delay_data);

            addr_cmd_delay_max = max(up_addr_cmd_delay_data, addr_cmd_delay_max);
            addr_cmd_delay_max = max(lu_addr_cmd_delay_data, addr_cmd_delay_max);
        }
    }

    addr_cmd_delay_coarse = SNPS_READ_FIELD(addr_cmd_delay_max, AT_DLY_COARSE);
    addr_cmd_delay_fine = SNPS_READ_FIELD(addr_cmd_delay_max, AT_DLY_FINE);

    if (0 == tmgcfg_freq_ratio) {
        addr_cmd_delay_calc = DIV_2(2 * addr_cmd_delay_coarse);
        addr_cmd_delay_remainder = addr_cmd_delay_coarse % 2;
    } else {
        addr_cmd_delay_calc = DIV_4(2 * addr_cmd_delay_coarse);
        addr_cmd_delay_remainder = addr_cmd_delay_coarse % 4;
    }

    // Round up the value
    if ((addr_cmd_delay_remainder != 0) || (addr_cmd_delay_fine > 0)) {
        addr_cmd_delay_calc += 1;
    }

    SNPS_LOG("[DFI Control Timing]PHY trained delay: %d",addr_cmd_delay_calc);

    for(channel = 0; channel < num_channels; channel++) {

        dfitmg0 = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(0, channel) + DFITMG0);
        dfi_t_ctrl_delay = SNPS_READ_FIELD(dfitmg0, DFITMG0_DFI_T_CTRL_DELAY);
        SNPS_LOG("[DFI Control Timing]Controller delay: ch %d dfi_t_ctrl_delay=%d", channel, dfi_t_ctrl_delay);

        dfi_t_ctrl_delay = dfi_t_ctrl_delay + addr_cmd_delay_calc;
        SNPS_LOG("[DFI Control Timing]Expected delay: ch %d dfi_t_ctrl_delay=%d", channel, dfi_t_ctrl_delay);

        SNPS_WRITE_FIELD(dfitmg0, DFITMG0_DFI_T_CTRL_DELAY, dfi_t_ctrl_delay);

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
        }

        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, channel) + DFITMG0, dfitmg0);

        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_LOG("Error in seq_post_qdyn_write");
            return false;
        }
    }

    return true;
}

#endif /* DDR5_PHY */
#endif /* DDRCTL_DDR */
