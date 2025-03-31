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


#include "dwc_cinit_workaround_macros.h"
#include "dwc_ddrctl_cinit_common_dfi_timings.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_defines.h"

/**
 * @brief function to setup the register field values for dfitmg0
 */
void dwc_ddrctl_cinit_common_prgm_REGB_FREQ_DFITMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg0,
        &REGB_FREQ_CH1(freq).dfitmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, dfi_t_ctrl_delay, ch, freq);

    // grab the pre-calculated vale
    QDYN.dfi_t_rddata_en[freq][ch] = PRE_CFG.dfi_t_rddata_en[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_t_rddata_en, ch, freq);
    QDYN.dfi_tphy_wrdata[freq][ch] =  hdlr->phy_timing_params.dfi_tphy_wrdata;
    QDYN_CFG_MATRIX(ptr, dfi_tphy_wrdata, ch, freq);

    // grab the pre-calculated vale
    QDYN.dfi_tphy_wrlat[freq][ch] = PRE_CFG.dfi_tphy_wrlat[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_tphy_wrlat, ch, freq);

    if (hdlr->ddrPhyType_m == DWC_LPDDR4X_MULTIPHY) {
        CONSTRAIN_MAX(ptr[ch]->dfi_tphy_wrdata, 8);
        CONSTRAIN_MAX(ptr[ch]->dfi_tphy_wrlat, 60);
    }

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dfitmg1
 */
void dwc_ddrctl_cinit_common_prgm_REGB_FREQ_DFITMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg1,
        &REGB_FREQ_CH1(freq).dfitmg1
    };
    uint32_t tmp = ptr[ch]->value;

    // calculate value dfi_t_wrdata_delay
    // This is specific to PHY Type 6, 7, 8
    uint32_t Trained_TxDQSDly = 0;
    uint32_t tSTAOFF = 0;
    uint32_t ratio;
    ddrTimingParameters_t *timing = &CFG->timingParams_m[freq][0];

    ratio = ddrctl_sw_get_ratio_factor(CFG, freq);

    // dfi_t_ctrl_delay is in DFI clock units, so multiply by ratio perform
    // equation in mem clks then convert to DFI units.
    if (IS_DDR5) {
        QDYN.dfi_t_wrdata_delay[freq][ch] = ratio * QDYN.dfi_t_ctrl_delay[freq][ch] + 14 + DIV_2(timing->burst_length) + Trained_TxDQSDly;
    #ifdef DDRCTL_EXT_SBECC_AND_CRC
        SNPS_LOG("original dfi_t_wrdata_delay=%u", QDYN.dfi_t_wrdata_delay[freq][ch]);
        QDYN.dfi_t_wrdata_delay[freq][ch] = QDYN.dfi_t_wrdata_delay[freq][ch] + (hdlr->del_tphy_wrlat+hdlr->del_tphy_wrdata);
        SNPS_LOG("new dfi_t_wrdata_delay=%u with WR DATA PIPELINE state of DFI RAS model", QDYN.dfi_t_wrdata_delay[freq][ch]);
    #endif
        QDYN.dfi_t_wrdata_delay[freq][ch] = CEIL(QDYN.dfi_t_wrdata_delay[freq][ch], ratio);
    }
    else if (IS_DDR4) {
        QDYN.dfi_t_wrdata_delay[freq][ch] = ratio * QDYN.dfi_t_ctrl_delay[freq][ch] + 6 + DIV_2(timing->burst_length) + Trained_TxDQSDly;
        QDYN.dfi_t_wrdata_delay[freq][ch] = CEIL(QDYN.dfi_t_wrdata_delay[freq][ch], ratio);
    }
#ifdef DDRCTL_LPDDR
    else if (IS_LPDDR4)
       //1:2 mode: RU[(tctrl_delay + (8+BL/2) +Trained_TxDqsDly)/2]
       //1:4 mode: RU[(tctrl_delay + (8+BL/2) +Trained_TxDqsDly)/4]
        QDYN.dfi_t_wrdata_delay[freq][ch] = CEIL((PRE_CFG.dfi_t_ctrl_delay_memclk[freq][ch] + 8 + DIV_2(timing->burst_length) + Trained_TxDQSDly),ratio);
#ifdef CINIT_LPDDR5
    else if (IS_LPDDR5)
        // NA for LPDDR5. Set to "twck_delay + BL/n_max - BL/n_min" instead.
        QDYN.dfi_t_wrdata_delay[freq][ch] = CEIL(PRE_CFG.dfi_twck_delay[freq][ch], ratio) + (timing->lpddr5_bl_n_max_tck - timing->lpddr5_bl_n_min_tck);
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    if (IS_RDIMM || IS_LRDIMM)
        QDYN.dfi_t_wrdata_delay[freq][ch] += tSTAOFF;

    QDYN_CFG_MATRIX(ptr, dfi_t_wrdata_delay, ch, freq);

    // Note scaling for freq ratio already taken care of in cinit_cal_dfi_timings
    QDYN.dfi_t_dram_clk_disable[freq][ch] = PRE_CFG.dfi_t_dram_clk_disable[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_t_dram_clk_disable, ch, freq);

    QDYN.dfi_t_dram_clk_enable[freq][ch] = PRE_CFG.dfi_t_dram_clk_enable[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_t_dram_clk_enable, ch, freq);


    SNPS_TRACE("Leaving");
}

#ifdef DDRCTL_CAPAR_RETRY
void dwc_ddrctl_cinit_common_prgm_REGB_FREQ_RETRYTMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RETRYTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).retrytmg1,
        &REGB_FREQ_CH1(freq).retrytmg1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.dfi_t_phy_rdlat[freq][ch] = PRE_CFG.dfi_t_phy_rdlat[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_t_phy_rdlat, ch, freq);
    SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_CAPAR_RETRY */



