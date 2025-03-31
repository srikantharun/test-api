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


/**
 * @detail The purpose of the functions in this file are to take the setting passed in structures in SubsysHdlr_t
 * and apply them to each of the registers in the controller memory map.
 * After each function is called a 32-bit value is ready to be written into the controller register map.
 * No APB bus cycles are actually executed by calling this methods.
 */

#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_lpddr54_dfi_timings.h"
#include "dwc_ddrctl_cinit_ddr54_dfi_timings.h"
#include "dwc_ddrctl_cinit_common_dfi_timings.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_defines.h"

#define DWC_USE_SET1_FOR_SET2_TMG
/**
 * @brief function to setup the register field values for dramset1tmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG0(uint32_t freq, uint32_t ch)
{
    DRAMSET1TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg0,
        &REGB_FREQ_CH1(freq).dramset1tmg0
    };
    uint32_t                tmp = ptr[ch]->value;
    ddrTimingParameters_t   *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4)
        QDYN.wr2pre[freq][ch] = PRE_CFG.wl[freq][ch] + 8 + PRE_CFG.twr[freq][ch] + 1;
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.wr2pre[freq][ch]  = PRE_CFG.wl[freq][ch] + timing->lpddr5_bl_n_min_tck;
        QDYN.wr2pre[freq][ch] += PRE_CFG.twr[freq][ch] + 1;
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        QDYN.wr2pre[freq][ch]  = PRE_CFG.cwl_x[freq] + DIV_2(timing->burst_length);
        QDYN.wr2pre[freq][ch] += PRE_CFG.twr[freq][ch] + timing->ddr4_tpl_tck;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN.wr2pre[freq][ch]  = PRE_CFG.cwl_x[freq] + DIV_2(timing->burst_length);
        QDYN.wr2pre[freq][ch] += PRE_CFG.twr[freq][ch] + QDYN.wr_crc_enable;
        QDYN.wr2pre[freq][ch] += CEIL(timing->ddr5_tdqs2dq_ps,SPD.tck_ps[freq]);
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

    QDYN_CFG_MATRIX(ptr, wr2pre, ch, freq);

    QDYN.t_faw[freq][ch] = PRE_CFG.tfaw[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_faw, ch, freq);

#ifdef DDRCTL_DDR4_OR_LPDDR
    if( IS_DDR4 || IS_LPDDR4 || IS_LPDDR5) {
        QDYN.t_ras_max[freq][ch] = PRE_CFG.t_ras_max[freq][ch];
        QDYN_CFG_MATRIX(ptr, t_ras_max, ch, freq);
        CONSTRAIN_MIN(ptr[ch]->t_ras_max, 1);    // cannot be zero
    }
#endif

    QDYN.t_ras_min[freq][ch] = PRE_CFG.t_ras_min[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ras_min, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG0, ptr[ch]->value);
    }
}

/**
 * @brief function to setup the register field values for dramset1tmg1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg1,
        &REGB_FREQ_CH1(freq).dramset1tmg1
    };
    uint8_t                 bl_div2;
    uint32_t                tmp = ptr[ch]->value;
    ddrTimingParameters_t   *timing = &hdlr->timingParams_m[freq][0];

    // BL/2 (Burst Length / 2)
    bl_div2 = DIV_2(timing->burst_length);

#ifdef MEMC_LPDDR5X
    if (SPD.use_lpddr5x && IS_LPDDR5) {
    QDYN.t_rcd_write[freq][ch] = PRE_CFG.t_rcd_write[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rcd_write, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->t_rcd_write, 1, 0xff);    // cannot be zero, 8 bits
    }
#endif /* MEMC_LPDDR5 */
    QDYN.t_xp[freq][ch] = PRE_CFG.txp[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_xp, ch, freq);

#ifdef DDRCTL_LPDDR
    if (IS_LPDDR4) {
        QDYN.rd2pre[freq][ch] = 8 - 8 + PRE_CFG.t_rtp[freq][ch];
    }
    if (IS_LPDDR5) {
        QDYN.rd2pre[freq][ch] = timing->lpddr5_bl_n_min_tck + PRE_CFG.t_rbtp[freq][ch];
    }
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        uint32_t ddr4_eq1_rd2pre, ddr4_eq2_rd2pre;
        // JEDEC DDR4: Read to precharge = tAL + max (4 *nCK, tRTP)
        // rd2pre is max of following two equations:
        // - AL + max(trtp, 4)
        // - RL + BL/2 - trp  (RL = AL+CL)
        ddr4_eq1_rd2pre = SPD.tAL + max(PRE_CFG.t_rtp[freq][ch], 4);
        ddr4_eq2_rd2pre = SPD.tAL + PRE_CFG.cl[freq] + bl_div2 - PRE_CFG.t_rp[freq][ch];
        QDYN.rd2pre[freq][ch] = max(ddr4_eq1_rd2pre, ddr4_eq2_rd2pre);
    }
#endif // CINIT_DDR4
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        uint32_t ddr5_eq1_rd2pre = 0, ddr5_eq2_rd2pre = 0;

        ddr5_eq1_rd2pre = PRE_CFG.t_rtp[freq][ch];

        if ((PRE_CFG.cl[freq] + bl_div2) > PRE_CFG.t_rp[freq][ch]) {
          ddr5_eq2_rd2pre = PRE_CFG.cl[freq] + bl_div2 - PRE_CFG.t_rp[freq][ch];
        }

        QDYN.rd2pre[freq][ch] = max(ddr5_eq1_rd2pre, ddr5_eq2_rd2pre);
    }
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */

    QDYN_CFG_MATRIX(ptr, rd2pre, ch, freq);

    QDYN.t_rc[freq][ch] = PRE_CFG.t_rc[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rc, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg2
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg2,
        &REGB_FREQ_CH1(freq).dramset1tmg2
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    // write latency
    if (IS_LPDDR4)
        QDYN.write_latency[freq][ch] = PRE_CFG.wl[freq][ch];
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5)
        QDYN.write_latency[freq][ch] = PRE_CFG.wl[freq][ch];
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

        if (hdlr->memCtrlr_m.ddr4_mr[freq].mr5.read_dbi == 1)
            QDYN.write_latency[freq][ch] = SPD.tAL_RDBI + PRE_CFG.cwl_x[freq];
        if (hdlr->memCtrlr_m.ddr4_mr[freq].mr5.read_dbi == 1)
            QDYN.write_latency[freq][ch] = SPD.tAL_RDBI + PRE_CFG.cwl_x[freq] + timing->ddr4_tpl_tck;
        else
            QDYN.write_latency[freq][ch] = SPD.tAL + PRE_CFG.cwl_x[freq] + timing->ddr4_tpl_tck;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN.write_latency[freq][ch] = PRE_CFG.cwl_x[freq];
    }
#endif /* CINIT_DDR5 */
#if !defined(CINIT_DDR4) && !defined(CINIT_DDR5)
    QDYN.write_latency[freq][ch] = SPD.tAL + PRE_CFG.cwl_x[freq];
#endif /* !defined(CINIT_DDR4) && !defined(CINIT_DDR5) */
#endif /* DDRCTL_DDR */

    QDYN_CFG_MATRIX(ptr, write_latency, ch, freq);

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        if (hdlr->memCtrlr_m.lpddr4_mr[freq].mr3.read_dbi == 1)
            QDYN.read_latency[freq][ch] = PRE_CFG.cl_dbi[freq];
        else
            QDYN.read_latency[freq][ch] = PRE_CFG.cl[freq];
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.read_latency[freq][ch] = PRE_CFG.rl[freq][ch];
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4)
        QDYN.read_latency[freq][ch] = SPD.tAL + PRE_CFG.cl[freq] + hdlr->timingParams_m[freq][0].ddr4_tpl_tck;
#endif  // CINIT_DDR4
#ifdef CINIT_DDR5
    if (IS_DDR5)
        QDYN.read_latency[freq][ch] = PRE_CFG.cl[freq];
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */

    QDYN_CFG_MATRIX(ptr, read_latency, ch, freq);

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4 && hdlr->memCtrlr_m.lpddr4_mr[freq].mr11.dq_odt > 0)
        QDYN.rd2wr[freq][ch] = PRE_CFG.rd2wr_odt[freq][ch];
    else
#endif
#endif /* DDRCTL_LPDDR */

    {
        QDYN.rd2wr[freq][ch] = PRE_CFG.rd2wr[freq][ch];
    }

    QDYN_CFG_MATRIX(ptr, rd2wr, ch, freq);

    QDYN.wr2rd[freq][ch] = PRE_CFG.wr2rd[freq][ch];

    QDYN_CFG_MATRIX(ptr, wr2rd, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg3
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg3,
        &REGB_FREQ_CH1(freq).dramset1tmg3
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef CINIT_DDR4
    if (IS_DDR4)
        QDYN.t_mr[freq][ch] = PRE_CFG.t_mod[freq][ch];
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5)
        QDYN.t_mr[freq][ch] = PRE_CFG.t_mr[freq][ch];
#endif
#if !defined(CINIT_DDR4) && !defined(CINIT_DDR5)
    QDYN.t_mr[freq][ch] = PRE_CFG.t_mr[freq][ch];
#endif /* !defined(CINIT_DDR4) && !defined(CINIT_DDR5) */
    QDYN_CFG_MATRIX(ptr, t_mr, ch, freq);

#ifdef DDRCTL_LPDDR
    QDYN.rd2mr[freq][ch] = PRE_CFG.rd2mr[freq][ch];
    QDYN_CFG_MATRIX(ptr, rd2mr, ch, freq);

    QDYN.wr2mr[freq][ch] = PRE_CFG.wr2mr[freq][ch];
    QDYN_CFG_MATRIX(ptr, wr2mr, ch, freq);
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg4
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG4_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg4,
        &REGB_FREQ_CH1(freq).dramset1tmg4
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_rcd[freq][ch] = PRE_CFG.t_rcd[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rcd, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->t_rcd, 1, 0x7f);    // cannot be zero, 7 bits

    QDYN.t_ccd[freq][ch] = PRE_CFG.t_ccd[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd, ch, freq);

    QDYN.t_rrd[freq][ch] = PRE_CFG.t_rrd[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rrd, ch, freq);

    QDYN.t_rp[freq][ch] = PRE_CFG.t_rp[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rp, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG4, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg5
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG5(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG5_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg5,
        &REGB_FREQ_CH1(freq).dramset1tmg5
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_cksrx[freq][ch] = PRE_CFG.t_cksrx[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cksrx, ch, freq);

    QDYN.t_cksre[freq][ch] = PRE_CFG.t_cksre[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cksre, ch, freq);

    QDYN.t_ckesr[freq][ch] = PRE_CFG.t_ckesr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ckesr, ch, freq);

    QDYN.t_cke[freq][ch] = PRE_CFG.t_cke[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cke, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG5, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg6
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG6(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG6_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg6,
        &REGB_FREQ_CH1(freq).dramset1tmg6
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ckcsx[freq][ch] = 0;
#if defined(CINIT_LPDDR4) || defined(CINIT_LPDDR5)
    if (IS_LPDDR4 || IS_LPDDR5)
        QDYN.t_ckcsx[freq][ch] = PRE_CFG.txp[freq][ch] + 2;
#endif
    QDYN_CFG_MATRIX(ptr, t_ckcsx, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG6, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG6(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dramset1tmg7
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG7(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG7_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg7,
        &REGB_FREQ_CH1(freq).dramset1tmg7
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.t_csh[freq][ch] = PRE_CFG.t_csh[freq][ch];
        QDYN_CFG_MATRIX(ptr, t_csh, ch, freq);

        QDYN.t_mrw_l[freq][ch] = PRE_CFG.t_mrw_l[freq][ch];
        QDYN_CFG_MATRIX(ptr, t_mrw_l, ch, freq);
    }
#endif  // CINIT_LPDDR5
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG7, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG7(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
/**
 * @brief function to setup the register field values for dramset1tmg8
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG8(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG8_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg8,
        &REGB_FREQ_CH1(freq).dramset1tmg8
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_xs_x32[freq][ch] = PRE_CFG.t_xs_min[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_xs_x32, ch, freq);

    QDYN.t_xs_dll_x32[freq][ch] = PRE_CFG.t_xs_dll_x32[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_xs_dll_x32, ch, freq);

    QDYN.t_xs_fast_x32[freq][ch] = PRE_CFG.t_xs_fast_min[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_xs_fast_x32, ch, freq);

    QDYN.t_xs_abort_x32[freq][ch] = PRE_CFG.t_xs_fast_min[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_xs_abort_x32, ch, freq);
    //must be less than or equal to t_xs_x32
    CONSTRAIN_MAX(ptr[ch]->t_xs_fast_x32, ptr[ch]->t_xs_x32);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG8, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* !DDRCTL_DDR */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG8(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg9
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG9(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG9_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg9,
        &REGB_FREQ_CH1(freq).dramset1tmg9
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        //wr_preamble
        QDYN_CFG_MATRIX(ptr, ddr4_wr_preamble, ch, freq);
        QDYN.t_ccd_s[freq][ch] = timing->ddr4_tccd_s_tck;
        QDYN.t_rrd_s[freq][ch] = timing->trrd_s_tck;
        QDYN.wr2rd_s[freq][ch] = PRE_CFG.wr2rd_s[freq][ch];
        // Calculate wr2rd_s
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN.t_ccd_s[freq][ch] = timing->ddr5_tccd_s_tck;
        QDYN.t_rrd_s[freq][ch] = timing->trrd_s_tck;
        QDYN.wr2rd_s[freq][ch] = PRE_CFG.wr2rd_s[freq][ch];
    }
#endif /* CINIT_DDR5 */

    QDYN_CFG_MATRIX(ptr, wr2rd_s, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_ccd_s, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rrd_s, ch, freq);
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.t_ccd_s[freq][ch] = timing->lpddr5_bl_n_min_tck;
        QDYN_CFG_MATRIX(ptr, t_ccd_s, ch, freq);
    }
#endif

    QDYN.t_rrd_s[freq][ch] = PRE_CFG.t_rrd_s[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rrd_s, ch, freq);
#endif /* DDRCTL_LPDDR */

    QDYN.wr2rd_s[freq][ch] = PRE_CFG.wr2rd_s[freq][ch];
    QDYN_CFG_MATRIX(ptr, wr2rd_s, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG9, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg10
 */
#if defined(DDRCTL_DDR4) && !defined(MEMC_CMD_RTN2IDLE)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG10(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
#ifdef CINIT_DDR4
    DRAMSET1TMG10_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg10,
        &REGB_FREQ_CH1(freq).dramset1tmg10
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_sync_gear[freq][ch] = PRE_CFG.t_sync_gear[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_sync_gear, ch, freq);

    QDYN.t_cmd_gear[freq][ch] = PRE_CFG.t_cmd_gear[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cmd_gear, ch, freq);

    QDYN.t_gear_setup[freq][ch] = PRE_CFG.t_gear_setup[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_gear_setup, ch, freq);

    QDYN.t_gear_hold[freq][ch] = PRE_CFG.t_gear_hold[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_gear_hold, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG10, ptr[ch]->value);
#endif // CINIT_DDR4
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && !MEMC_CMD_RTN2IDLE */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG10(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && !MEMC_CMD_RTN2IDLE */

/**
 * @brief function to setup the register field values for dramset1tmg11
 */
#ifdef DDRCTL_DDR4
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG11(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
#ifdef CINIT_DDR4
    DRAMSET1TMG11_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg11,
        &REGB_FREQ_CH1(freq).dramset1tmg11
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.post_mpsm_gap_x32[freq][ch] = PRE_CFG.post_mpsm_gap_x32[freq][ch];
    QDYN_CFG_MATRIX(ptr, post_mpsm_gap_x32, ch, freq);

    QDYN.t_mpx_lh[freq][ch] = PRE_CFG.t_mpx_lh[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mpx_lh, ch, freq);

    QDYN.t_mpx_s[freq][ch]  = PRE_CFG.t_mpx_s[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mpx_s, ch, freq);

    QDYN.t_ckmpe[freq][ch]  = PRE_CFG.t_ckmpe[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ckmpe, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG11, ptr[ch]->value);
#endif // CINIT_DDR4
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG11(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg12
 */
#ifdef DDRCTL_DDR4_OR_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG12(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG12_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg12,
        &REGB_FREQ_CH1(freq).dramset1tmg12
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_LPDDR
    QDYN.t_cmdcke[freq][ch] = PRE_CFG.t_cmdcke[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cmdcke, ch, freq);
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        QDYN.t_wr_mpr[freq][ch] = PRE_CFG.t_wr_mpr[freq][ch];

        QDYN.t_mrd_pda[freq][ch] = PRE_CFG.t_mrd_pda[freq][ch];
        if (QDYN.t_mrd_pda[freq][ch] < 16)
            QDYN.t_mrd_pda[freq][ch] = 16;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN.t_mrd_pda[freq][ch] = 0;
    }
#endif /* CINIT_DDR5 */
    QDYN_CFG_MATRIX(ptr, t_wr_mpr, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_mrd_pda, ch, freq);
#endif /* DDRCTL_DDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG12, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG12(uint32_t freq, uint32_t ch)
{
};
#endif // DDRCTL_DDR4_OR_LPDDR
/**
 * @brief function to setup the register field values for dramset1tmg13
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG13(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG13_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg13,
        &REGB_FREQ_CH1(freq).dramset1tmg13
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_LPDDR
    QDYN.odtloff[freq][ch] = PRE_CFG.odtloff[freq][ch];
    QDYN_CFG_MATRIX(ptr, odtloff, ch, freq);
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4)
        QDYN.t_ccd_mw[freq][ch] = timing->lpddr4_tccdmw;
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5)
        QDYN.t_ccd_mw[freq][ch] = timing->lpddr5_tccdmw_tck;
#endif
    QDYN_CFG_MATRIX(ptr, t_ccd_mw, ch, freq);
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4)
        QDYN.t_ppd[freq][ch] = timing->lpddr4_tppd;
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5)
        QDYN.t_ppd[freq][ch] = timing->lpddr5_tppd_tck;
#endif /* CINIT_LPDDR5 */
    QDYN_CFG_MATRIX(ptr, t_ppd, ch, freq);
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
    QDYN.t_ccd_w2[freq][ch] = PRE_CFG.t_ccd_w2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w2, ch, freq);
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN.t_ppd[freq][ch] = timing->ddr5_tppd_tck;
        QDYN_CFG_MATRIX(ptr, t_ppd, ch, freq);
    }
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG13, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg14
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG14(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG14_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg14,
        &REGB_FREQ_CH1(freq).dramset1tmg14
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_xsr, ch, freq);

    if (hdlr->enable_non_jedec_tck == 0) {
        uint32_t tck_ps = SPD.tck_ps[freq];
        uint8_t dvfsc_type = hdlr->memCtrlr_m.lpddr5_mr[freq].mr19.dvfsc; // 0=disabled 1=dvfsc 2=enhanced dvfsc
        uint32_t min_t_xsr = dwc_cinit_get_min_t_xsr(hdlr, tck_ps, dvfsc_type);
        #if !(defined(LPDDR_2MC1PHY) && defined(DWC_DDRCTL_CINIT_CPU_DPI_MODE))
          CONSTRAIN_MIN(ptr[ch]->t_xsr, min_t_xsr);
        #endif
    }

#ifdef LPDDR45_DQSOSC_EN
#if defined(CINIT_LPDDR4) || defined(CINIT_LPDDR5)
    if (IS_LPDDR4 || IS_LPDDR5) {
        QDYN.t_osco[freq][ch] = PRE_CFG.t_osco[freq][ch];
        QDYN_CFG_MATRIX(ptr, t_osco, ch, freq);
    }
#endif
#endif /* LPDDR45_DQSOSC_EN */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG14, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG14(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dramset1tmg15
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG15(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG15_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg15,
        &REGB_FREQ_CH1(freq).dramset1tmg15
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, en_dfi_lp_t_stab, ch, freq);

#ifdef UMCTL2_HWFFC_EN
    QDYN_CFG_MATRIX(ptr, en_hwffc_t_stab, ch, freq);
#endif /* UMCTL2_HWFFC_EN */
#ifdef CINIT_DDR5
    if (IS_DDR5 && (IS_LRDIMM || IS_RDIMM))
        QDYN.t_stab_x32[freq][ch] = CEIL(PRE_CFG.t_stab01[freq][ch], 32);
#endif  // CINIT_DDR5
    QDYN_CFG_MATRIX(ptr, t_stab_x32, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG15, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG15(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg16
 */
#ifdef UMCTL2_CID_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG16(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG16_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg16,
        &REGB_FREQ_CH1(freq).dramset1tmg16
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ccd_dlr[freq][ch] = PRE_CFG.t_ccd_dlr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_dlr, ch, freq);

    QDYN.t_rrd_dlr[freq][ch] = PRE_CFG.t_rrd_dlr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rrd_dlr, ch, freq);

    QDYN.t_faw_dlr[freq][ch] = PRE_CFG.t_faw_dlr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_faw_dlr, ch, freq);

/// @todo this code fragment is not verified
#ifdef DDRCTL_CAPAR_RETRY
    QDYN.t_rp_ca_parity[freq][ch] = 5; /// @todo dramset1tmg16 is missing this code and value also. The
                                         // 5 value is the register reset setting
    QDYN_CFG_MATRIX(ptr, t_rp_ca_parity, ch, freq);
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG16, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_CID_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG16(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_CID_EN */

/**
 * @brief function to setup the register field values for dramset1tmg17
 */
#ifdef UMCTL2_HWFFC_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG17(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG17_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg17,
        &REGB_FREQ_CH1(freq).dramset1tmg17
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_vrcg_enable[freq][ch] = PRE_CFG.t_vrcg_enable[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_vrcg_enable, ch, freq);

    QDYN.t_vrcg_disable[freq][ch] = PRE_CFG.t_vrcg_disable[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_vrcg_disable, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG17, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HWFFC_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG17(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_HWFFC_EN */

/**
 * @brief function to setup the register field values for dramset1tmg18
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG18(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG18_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg18,
        &REGB_FREQ_CH1(freq).dramset1tmg18
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_pd[freq][ch] = PRE_CFG.t_pd[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_pd, ch, freq);

    QDYN.t_mpsmx[freq][ch] = PRE_CFG.t_mpsmx[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mpsmx, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG18, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG18(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */


/**
 * @brief function to setup the register field values for dramset1tmg20
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG20(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG20_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg20,
        &REGB_FREQ_CH1(freq).dramset1tmg20
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_cpded[freq][ch] = PRE_CFG.t_cpded[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cpded, ch, freq);

    QDYN.t_casrx[freq][ch] = PRE_CFG.t_casrx[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_casrx, ch, freq);

    QDYN.t_csh_srexit[freq][ch] = PRE_CFG.t_csh_srexit[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_csh_srexit, ch, freq);

    QDYN.t_csl_srexit[freq][ch] = PRE_CFG.t_csl_srexit[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_csl_srexit, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG20, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG20(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg21
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG21(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG21_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg21,
        &REGB_FREQ_CH1(freq).dramset1tmg21
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_csl[freq][ch] = PRE_CFG.t_csl[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_csl, ch, freq);

    QDYN.t_mpc_cs[freq][ch] = PRE_CFG.t_mpc_cs[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mpc_cs, ch, freq);

    QDYN.t_mpc_setup[freq][ch] = PRE_CFG.t_mpc_setup[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mpc_setup, ch, freq);

    QDYN.t_mpc_hold[freq][ch] = PRE_CFG.t_mpc_hold[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mpc_hold, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG21, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG21(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg22
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG22(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG22_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg22,
        &REGB_FREQ_CH1(freq).dramset1tmg22
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_wr2rd_dpr[freq][ch] = PRE_CFG.t_wr2rd_dpr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr2rd_dpr, ch, freq);

    QDYN.t_rd2wr_dpr[freq][ch] = PRE_CFG.t_rd2wr_dpr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rd2wr_dpr, ch, freq);

#ifdef UMCTL2_CID_EN
    QDYN.t_wr2rd_dlr[freq][ch] = PRE_CFG.t_wr2rd_dlr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr2rd_dlr, ch, freq);

    QDYN.t_rd2wr_dlr[freq][ch] = PRE_CFG.t_rd2wr_dlr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rd2wr_dlr, ch, freq);
#endif /* UMCTL2_CID_EN */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG22, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG22(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg23
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG23(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG23_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg23,
        &REGB_FREQ_CH1(freq).dramset1tmg23
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

    DYN.t_xsr_dsm_x1024[freq][ch] = CEIL((timing->lpddr5_txsr_dsm_us * 1000000 / SPD.tck_ps[freq]), 1024);
    DYN_CFG_MATRIX(ptr, t_xsr_dsm_x1024, ch, freq);

    DYN.t_pdn[freq][ch] = PRE_CFG.t_pdn[freq][ch];
    DYN_CFG_MATRIX(ptr, t_pdn, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG23, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG23(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dramset1tmg24
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG24(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG24_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg24,
        &REGB_FREQ_CH1(freq).dramset1tmg24
    };
    uint32_t tmp = ptr[ch]->value;

    // 8Bank is not allowed
    QDYN.bank_org[freq][ch] = SPD.lpddr5_bk_bg_org[freq] == DWC_LPDDR5_4BK_4BG ? 0 : 2;
    QDYN.max_rd_sync[freq][ch] = PRE_CFG.max_rd_sync[freq][ch];
    QDYN.max_wr_sync[freq][ch] = PRE_CFG.max_wr_sync[freq][ch];

    QDYN.rd2wr_s[freq][ch] = PRE_CFG.rd2wr_s[freq][ch];

    QDYN_CFG_MATRIX(ptr, bank_org, ch, freq);

    QDYN_CFG_MATRIX(ptr, rd2wr_s, ch, freq);

    QDYN_CFG_MATRIX(ptr, max_rd_sync, ch, freq);

    QDYN_CFG_MATRIX(ptr, max_wr_sync, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG24, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG24(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dramset1tmg25
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG25(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG25_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg25,
        &REGB_FREQ_CH1(freq).dramset1tmg25
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_LPDDR
    QDYN.lpddr4_diff_bank_rwa2pre[freq][ch] = PRE_CFG.lpddr4_diff_bank_rwa2pre[freq][ch];
    QDYN_CFG_MATRIX(ptr, lpddr4_diff_bank_rwa2pre, ch, freq);
#endif /* DDRCTL_LPDDR */

    QDYN.wra2pre[freq][ch] = PRE_CFG.wra2pre[freq][ch];
    QDYN.rda2pre[freq][ch] = PRE_CFG.rda2pre[freq][ch];

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        QDYN.wra2pre[freq][ch] = QDYN.wr2pre[freq][ch];
        QDYN.rda2pre[freq][ch] = QDYN.rd2pre[freq][ch];
    }
#endif  // CINIT_DDR4
#endif /* DDRCTL_DDR */

    QDYN_CFG_MATRIX(ptr, wra2pre, ch, freq);

    QDYN_CFG_MATRIX(ptr, rda2pre, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG25, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset1tmg26
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG26(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG26_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg26,
        &REGB_FREQ_CH1(freq).dramset1tmg26
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ccd_w_s[freq][ch] = PRE_CFG.t_ccd_w_s[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w_s, ch, freq);

    QDYN.t_ccd_r_s[freq][ch] = PRE_CFG.t_ccd_r_s[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_r_s, ch, freq);

    QDYN.t_ccd_w[freq][ch] = PRE_CFG.t_ccd_w[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w, ch, freq);

    QDYN.t_ccd_r[freq][ch] = PRE_CFG.t_ccd_r_l[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_r, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG26, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG26(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg27
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG27(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG27_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg27,
        &REGB_FREQ_CH1(freq).dramset1tmg27
    };
    uint32_t tmp = ptr[ch]->value;
    uint32_t min_t_ecs;

    QDYN.t_mrr2mpc[freq][ch] = PRE_CFG.t_mrr2mpc[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mrr2mpc, ch, freq);

    min_t_ecs = (110000 / SPD.tck_ps[freq]) + (110000 % SPD.tck_ps[freq] != 0);
    ptr[ch]->t_ecsc = min_t_ecs;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG27, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG27(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dramset1tmg28
 */
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG28(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG28_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg28,
        &REGB_FREQ_CH1(freq).dramset1tmg28
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_srx2srx[freq][ch] = PRE_CFG.t_srx2srx[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_srx2srx, ch, freq);

    QDYN.t_cpded2srx[freq][ch] = PRE_CFG.t_cpded2srx[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cpded2srx, ch, freq);

    QDYN.t_cssr[freq][ch] = PRE_CFG.t_cssr[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_cssr, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG28, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG28(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH */

/**
 * @brief function to setup the register field values for dramset1tmg29
 */
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG29(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG29_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg29,
        &REGB_FREQ_CH1(freq).dramset1tmg29
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ckact[freq][ch] = PRE_CFG.t_ckact[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ckact, ch, freq);

    QDYN.t_ckoff[freq][ch] = PRE_CFG.t_ckoff[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ckoff, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG29, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG29(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH */

/**
 * @brief function to setup the register field values for dramset1tmg30
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG30(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG30_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg30,
        &REGB_FREQ_CH1(freq).dramset1tmg30
    };
    uint32_t tmp = ptr[ch]->value;

    // 8Bank is not allowed
    if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.dq_odt > 0)
        QDYN.mrr2wr[freq][ch] = PRE_CFG.mrr2wr_odt[freq][ch];
    else
        QDYN.mrr2wr[freq][ch] = PRE_CFG.mrr2wr[freq][ch];

    QDYN.mrr2rd[freq][ch] = PRE_CFG.mrr2rd[freq][ch];
    QDYN_CFG_MATRIX(ptr, mrr2rd, ch, freq);

    QDYN.mrr2mrw[freq][ch] = PRE_CFG.mrr2mrw[freq][ch];
    QDYN_CFG_MATRIX(ptr, mrr2wr, ch, freq);

    QDYN_CFG_MATRIX(ptr, mrr2mrw, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG30, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG30(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dramset1tmg31
 */
#if defined(MEMC_DDR5) && defined(DDRCTL_HW_RFM_CTRL)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG31(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG31_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg31,
        &REGB_FREQ_CH1(freq).dramset1tmg31
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, rfm_raaimt, ch, freq);

    QDYN_CFG_MATRIX(ptr, rfm_raa_thr, ch, freq);

    QDYN_CFG_MATRIX(ptr, rfm_raa_ref_decr, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG31, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_HW_RFM_CTRL */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG31(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_HW_RFM_CTRL */

/**
 * @brief function to setup the register field values for DRAMSET1TMG32
 */
#if defined(DDRCTL_LPDDR) && defined(MEMC_NUM_RANKS_GT_1)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG32(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG32_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg32,
        &REGB_FREQ_CH1(freq).dramset1tmg32
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.ws_off2ws_fs[freq][ch] = PRE_CFG.ws_off2ws_fs[freq][ch];
    QDYN_CFG_MATRIX(ptr, ws_off2ws_fs, ch, freq);

    QDYN.t_wcksus[freq][ch] = PRE_CFG.t_wcksus[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wcksus, ch, freq);

    QDYN.ws_fs2wck_sus[freq][ch] = PRE_CFG.ws_fs2wck_sus[freq][ch];
    QDYN_CFG_MATRIX(ptr, ws_fs2wck_sus, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG32, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR && MEMC_NUM_RANKS_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG32(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR && MEMC_NUM_RANKS_GT_1 */

/**
 * @brief function to setup the register field values for DRAMSET1TMG33
 */
#if defined(DDRCTL_DDR5CTL) && defined(DDRCTL_DDR5CTL_HIGHSPEED)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG33(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG33_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg33,
        &REGB_FREQ_CH1(freq).dramset1tmg33
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_wr2rd_m[freq][ch] = PRE_CFG.t_wr2rd_m[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr2rd_m, ch, freq);

    QDYN.t_ccd_w_m[freq][ch] = PRE_CFG.t_ccd_w_m[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w_m, ch, freq);

    QDYN.t_ccd_r_m[freq][ch] = PRE_CFG.t_ccd_r_m[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_r_m, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG33, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG33(uint32_t freq, uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for DRAMSET1TMG34
 */
#if defined(DDRCTL_LPDDR) && defined(MEMC_BURST_LENGTH_32)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG34(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG34_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg34,
        &REGB_FREQ_CH1(freq).dramset1tmg34
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

    QDYN.t_ccd_blx2[freq][ch] = PRE_CFG.t_ccd_blx2[freq][ch];
    QDYN.wr2rd_blx2[freq][ch] = PRE_CFG.wr2rd_blx2[freq][ch];
    if (IS_LPDDR4 && hdlr->memCtrlr_m.lpddr4_mr[freq].mr11.dq_odt > 0)
        QDYN.rd2wr_blx2[freq][ch] = PRE_CFG.rd2wr_odt_blx2[freq][ch];
    else
        QDYN.rd2wr_blx2[freq][ch] = PRE_CFG.rd2wr_blx2[freq][ch];
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        QDYN.t_ccd_mw_blx2[freq][ch] = timing->lpddr4_tccdmw_bl32;
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.t_ccd_mw_blx2[freq][ch] = timing->lpddr5_tccdmw_bl32_tck;
    }
#endif /* CINIT_LPDDR5 */

    QDYN_CFG_MATRIX(ptr, t_ccd_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, wr2rd_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, rd2wr_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, t_ccd_mw_blx2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG34, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG34(uint32_t freq, uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for DRAMSET1TMG35
 */
#if defined(DDRCTL_LPDDR) && defined(MEMC_BURST_LENGTH_32)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG35(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG35_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg35,
        &REGB_FREQ_CH1(freq).dramset1tmg35
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        QDYN.wr2pre_blx2[freq][ch] = PRE_CFG.wl[freq][ch] + 16 + PRE_CFG.twr[freq][ch] + 1;
        QDYN.rd2pre_blx2[freq][ch] = 16 - 8 + PRE_CFG.t_rtp[freq][ch];
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.wr2pre_blx2[freq][ch] = PRE_CFG.wl[freq][ch] + timing->lpddr5_bl_n_min_bl32_tck + PRE_CFG.twr[freq][ch] + 1;
        QDYN.rd2pre_blx2[freq][ch] = 16 - 8 + PRE_CFG.t_rtp[freq][ch];
    }
#endif /* CINIT_LPDDR5 */
    QDYN.wra2pre_blx2[freq][ch] = PRE_CFG.wra2pre_blx2[freq][ch];
    QDYN.rda2pre_blx2[freq][ch] = PRE_CFG.rda2pre_blx2[freq][ch];

    QDYN_CFG_MATRIX(ptr, wr2pre_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, rd2pre_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, wra2pre_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, rda2pre_blx2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG35, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG35(uint32_t freq, uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for DRAMSET1TMG36
 */
#if defined(DDRCTL_LPDDR) && defined(MEMC_BURST_LENGTH_32)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG36(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG36_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg36,
        &REGB_FREQ_CH1(freq).dramset1tmg36
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef CINIT_LPDDR5
    QDYN.t_ccd_s_blx2[freq][ch] = (SPD.lpddr5_bk_bg_org[freq] == DWC_LPDDR5_4BK_4BG) ? 2 : timing->lpddr5_bl_n_min_bl32_tck;
    QDYN.wr2rd_s_blx2[freq][ch] = PRE_CFG.wr2rd_s_blx2[freq][ch];
    QDYN.rd2wr_s_blx2[freq][ch] = PRE_CFG.rd2wr_s_blx2[freq][ch];
#endif

    QDYN_CFG_MATRIX(ptr, t_ccd_s_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, wr2rd_s_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, rd2wr_s_blx2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG36, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG36(uint32_t freq, uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for DRAMSET1TMG37
 */
#if defined(DDRCTL_LPDDR) && defined(MEMC_BURST_LENGTH_32)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG37(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG37_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg37,
        &REGB_FREQ_CH1(freq).dramset1tmg37
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.rd2mr_blx2[freq][ch] = PRE_CFG.rd2mr_blx2[freq][ch];
    QDYN.wr2mr_blx2[freq][ch] = PRE_CFG.wr2mr_blx2[freq][ch];

#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
       QDYN.max_rd_sync_blx2[freq][ch] = PRE_CFG.max_rd_sync_blx2[freq][ch];
       QDYN.max_wr_sync_blx2[freq][ch] = PRE_CFG.max_wr_sync_blx2[freq][ch];
    }
#endif /* CINIT_LPDDR5 */

    QDYN_CFG_MATRIX(ptr, rd2mr_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, wr2mr_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, max_rd_sync_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, max_wr_sync_blx2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG37, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG37(uint32_t freq, uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for DRAMSET1TMG38
 */
#if defined(DDRCTL_LPDDR) && defined(MEMC_BURST_LENGTH_32) && defined(MEMC_NUM_RANKS_GT_1)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG38(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG38_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset1tmg38,
        &REGB_FREQ_CH1(freq).dramset1tmg38
    };
    uint32_t tmp = ptr[ch]->value;

    uint32_t wr_gap_min, rd_gap_min;

#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        wr_gap_min = PRE_CFG.odtloff[freq][ch] - PRE_CFG.odtlon[freq][ch] - 16 + 1;
        rd_gap_min = 4 + hdlr->memCtrlr_m.lpddr4_mr[freq].mr1.rd_postamble;

        // dcheck if min is being violated.
        // then overwrite with min
        if (wr_gap_min > QDYN.diff_rank_wr_gap_blx2[freq][ch]) {
            SNPS_LOG("%u: attempt to set diff_rank_wr_gap_blx2 = %u less than min", freq, QDYN.diff_rank_wr_gap_blx2[freq][ch]);
            QDYN.diff_rank_wr_gap_blx2[freq][ch] = wr_gap_min;
        }
        if (rd_gap_min > QDYN.diff_rank_rd_gap_blx2[freq][ch]) {
            QDYN.diff_rank_rd_gap_blx2[freq][ch] = rd_gap_min;
        }

        QDYN.wr2rd_dr_blx2[freq][ch] = PRE_CFG.wr2rd_dr_blx2[freq][ch];
        QDYN.rd2wr_dr_blx2[freq][ch] = QDYN.rd2wr_blx2[freq][ch];
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.dq_odt > 0) {    // ODT ON
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1
                QDYN.wr2rd_dr_blx2[freq][ch] = PRE_CFG.wr2rd_dr_wck_on_odt_blx2[freq][ch];
                QDYN.rd2wr_dr_blx2[freq][ch] = PRE_CFG.rd2wr_dr_wck_on_odt_blx2[freq][ch];
            } else {            // WCK_ON = 0
                QDYN.wr2rd_dr_blx2[freq][ch] = PRE_CFG.wr2rd_dr_odt_blx2[freq][ch];
                QDYN.rd2wr_dr_blx2[freq][ch] = PRE_CFG.rd2wr_dr_odt_blx2[freq][ch];
            }
        } else {                // ODT OFF
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1
                QDYN.wr2rd_dr_blx2[freq][ch] = PRE_CFG.wr2rd_dr_wck_on_blx2[freq][ch];
                QDYN.rd2wr_dr_blx2[freq][ch] = PRE_CFG.rd2wr_dr_wck_on_blx2[freq][ch];
            } else {            // WCK_ON = 0
                QDYN.wr2rd_dr_blx2[freq][ch] = PRE_CFG.wr2rd_dr_blx2[freq][ch];
                QDYN.rd2wr_dr_blx2[freq][ch] = PRE_CFG.rd2wr_dr_blx2[freq][ch];
            }
        }
    } 
#endif /* CINIT_LPDDR5 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.dq_odt > 0) {    //DQ ODT ON
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1 
               if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.nt_odt && hdlr->memCtrlr_m.lpddr5_mr[freq].mr41.nt_dq_odt>0 ) {        // WCK_ON = 1 && DQ ODT && NT ODT && ENHANCED NT_ODT
                   QDYN.diff_rank_wr_gap_blx2[freq][ch] = PRE_CFG.diff_rank_wr_gap_wck_on_dq_odt_nt_odt_blx2[freq][ch];
                   QDYN.diff_rank_rd_gap_blx2[freq][ch] = PRE_CFG.diff_rank_rd_gap_wck_on_dq_odt_nt_odt_blx2[freq][ch];
               } else {            // WCK_ON = 1 && DQ_ODT
                   QDYN.diff_rank_wr_gap_blx2[freq][ch] = PRE_CFG.diff_rank_wr_gap_wck_on_odt_blx2[freq][ch];
                   QDYN.diff_rank_rd_gap_blx2[freq][ch] = PRE_CFG.diff_rank_rd_gap_wck_on_odt_blx2[freq][ch];
               }
            } else {            // WCK_ON = 0 && DQ ODT
                QDYN.diff_rank_wr_gap_blx2[freq][ch] = PRE_CFG.diff_rank_wr_gap_odt_blx2[freq][ch];
                QDYN.diff_rank_rd_gap_blx2[freq][ch] = PRE_CFG.diff_rank_rd_gap_odt_blx2[freq][ch];
            }
        } else {                // ODT OFF
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1
                QDYN.diff_rank_wr_gap_blx2[freq][ch] = PRE_CFG.diff_rank_wr_gap_wck_on_blx2[freq][ch];
                QDYN.diff_rank_rd_gap_blx2[freq][ch] = PRE_CFG.diff_rank_rd_gap_wck_on_blx2[freq][ch];
            } else {            // WCK_ON = 0
                QDYN.diff_rank_wr_gap_blx2[freq][ch] = PRE_CFG.diff_rank_wr_gap_blx2[freq][ch];
                QDYN.diff_rank_rd_gap_blx2[freq][ch] = PRE_CFG.diff_rank_rd_gap_blx2[freq][ch];
            }
        }
    } 
#endif /* CINIT_LPDDR5 */

    QDYN_CFG_MATRIX(ptr, wr2rd_dr_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, rd2wr_dr_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, diff_rank_rd_gap_blx2, ch, freq);
    QDYN_CFG_MATRIX(ptr, diff_rank_wr_gap_blx2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET1TMG38, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG38(uint32_t freq, uint32_t ch)
{
};
#endif


/**
 * @brief function to setup the register field values for RANK_SWITCH_TIMING_CONTROL0
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_1)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANK_SWITCH_TIMING_CONTROL0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rank_switch_timing_control0,
        &REGB_FREQ_CH1(freq).rank_switch_timing_control0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r1r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r0r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r1r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r0r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r1r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r0r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r1r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r0r1, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANK_SWITCH_TIMING_CONTROL0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_1 */

/**
 * @brief function to setup the register field values for rank_switch_timing_control1
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANK_SWITCH_TIMING_CONTROL1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rank_switch_timing_control1,
        &REGB_FREQ_CH1(freq).rank_switch_timing_control1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r2r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r0r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r2r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r0r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r2r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r0r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r2r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r0r2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANK_SWITCH_TIMING_CONTROL1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */

/**
 * @brief function to setup the register field values for rank_switch_timing_control2
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANK_SWITCH_TIMING_CONTROL2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rank_switch_timing_control2,
        &REGB_FREQ_CH1(freq).rank_switch_timing_control2
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r3r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r0r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r3r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r0r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r3r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r0r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r3r0, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r0r3, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANK_SWITCH_TIMING_CONTROL2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL2(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */

/**
 * @brief function to setup the register field values for rank_switch_timing_control3
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANK_SWITCH_TIMING_CONTROL3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rank_switch_timing_control3,
        &REGB_FREQ_CH1(freq).rank_switch_timing_control3
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r2r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r1r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r2r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r1r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r2r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r1r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r2r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r1r2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANK_SWITCH_TIMING_CONTROL3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL3(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */

/**
 * @brief function to setup the register field values for rank_switch_timing_control4
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANK_SWITCH_TIMING_CONTROL4_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rank_switch_timing_control4,
        &REGB_FREQ_CH1(freq).rank_switch_timing_control4
    };
    uint32_t tmp = ptr[ch]->value;


    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r3r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r1r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r3r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r1r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r3r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r1r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r3r1, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r1r3, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANK_SWITCH_TIMING_CONTROL4, ptr[ch]->value);
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL4(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */

/**
 * @brief function to setup the register field values for rank_switch_timing_control5
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL5(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANK_SWITCH_TIMING_CONTROL5_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rank_switch_timing_control5,
        &REGB_FREQ_CH1(freq).rank_switch_timing_control5
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r3r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2wr_gap_r2r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r3r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2wr_gap_r2r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r3r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_wr2rd_gap_r2r3, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r3r2, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rd2rd_gap_r2r3, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANK_SWITCH_TIMING_CONTROL5, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL5(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 */

/**
 * @brief function to setup the register field values for dfiupdtmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG0(void)
{
    DFIUPDTMG0_t *const ptr = &REGB_FREQ_CH0(0).dfiupdtmg0;
    uint32_t tmp = ptr->value;

    STATIC.dfi_t_ctrlup_max = hdlr->phy_timing_params.dfi_t_ctrlup_max;

    STATIC.dfi_t_ctrlup_min = hdlr->phy_timing_params.dfi_t_ctrlup_min;

    STATIC_CFG(ptr, dfi_ctrlup_gap);

    STATIC_CFG(ptr, dfi_t_ctrlup_max);

    STATIC_CFG(ptr, dfi_t_ctrlup_min);

    if (hdlr->ddrPhyType_m == DWC_LPDDR54_PHY || hdlr->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
        // Table 5-6 LPDDR54 Utility block (PUB) databook (in DfiClks)
        CONSTRAIN_MIN(ptr->dfi_t_ctrlup_max, 0x18);    // min value
        CONSTRAIN_MIN(ptr->dfi_t_ctrlup_min, 0x01);    // min value
    } else {
        CONSTRAIN_MIN(ptr->dfi_t_ctrlup_max, 0x0b);    // min value
        CONSTRAIN_MIN(ptr->dfi_t_ctrlup_min, 0x01);    // min value
    }

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 0) + DFIUPDTMG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 1) + DFIUPDTMG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
}

/**
 * @brief function to setup the register field values for dfitmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    dwc_ddrctl_cinit_common_prgm_REGB_FREQ_DFITMG0(freq,ch);
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dfitmg1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg1,
        &REGB_FREQ_CH1(freq).dfitmg1
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_DDR
    // calculate value dfi_t_cmd_lat
    /// @todo doubl dcheck CAL mode
    if (IS_DDR4) {
        if (hdlr->memCtrlr_m.ddr4_mr[freq].mr4.cal == 0) {
            QDYN.dfi_t_cmd_lat[freq][ch] = 0;
        } else {
            uint32_t cal_cycles;

            cal_cycles = get_cal_cycles(hdlr->memCtrlr_m.ddr4_mr[freq].mr4.cal);
            if (IS_RDIMM || IS_LRDIMM)
                QDYN.dfi_t_cmd_lat[freq][ch] = cal_cycles + PRE_CFG.cmd_lat_adder[freq][ch];
            else
                QDYN.dfi_t_cmd_lat[freq][ch] = cal_cycles;
        }
    } else {
        QDYN.dfi_t_cmd_lat[freq][ch] = 0;
    }

    QDYN_CFG_MATRIX(ptr, dfi_t_cmd_lat, ch, freq);
    CONSTRAIN_MAX(ptr[ch]->dfi_t_cmd_lat, 8);

#ifdef CINIT_DDR4
    // calculate value dfi_t_parin_lat
    if (IS_DDR4) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

        if (IS_RDIMM || IS_LRDIMM) {
            QDYN.dfi_t_parin_lat[freq][ch] = 1;
        } else {
            if (timing->ddr4_tpl_tck == 0) {
                // can be 0-3 ??
                CONSTRAIN_MAX(QDYN.dfi_t_parin_lat[freq][ch], 3);
            } else {
                QDYN.dfi_t_parin_lat[freq][ch] = 0;
            }
        }
    }
#endif  // CINIT_DDR4
    QDYN_CFG_MATRIX(ptr, dfi_t_parin_lat, ch, freq);
#endif /* DDRCTL_DDR */

    dwc_ddrctl_cinit_common_prgm_REGB_FREQ_DFITMG1(freq,ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dfitmg2
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");

    DFITMG2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg2,
        &REGB_FREQ_CH1(freq).dfitmg2
    };
    uint32_t tmp = ptr[ch]->value;

    if (IS_DDR4) {
        QDYN.dfi_tphy_wrcslat[freq][ch] = QDYN.dfi_tphy_wrlat[freq][ch] + QDYN.dfi_t_cmd_lat[freq][ch];
        QDYN.dfi_tphy_rdcslat[freq][ch] = QDYN.dfi_t_rddata_en[freq][ch] + QDYN.dfi_t_cmd_lat[freq][ch];
    } else {
        QDYN.dfi_tphy_wrcslat[freq][ch] = QDYN.dfi_tphy_wrlat[freq][ch];
        QDYN.dfi_tphy_rdcslat[freq][ch] = QDYN.dfi_t_rddata_en[freq][ch];
    }

#ifdef DDRCTL_EXT_SBECC_AND_CRC
    // Override the dfi_tphy_wrcslat to original value if dfi_tphy_wrlat is programmed a smaller value.
      if (hdlr->en_dfi_ras_model == 1) {
      QDYN.dfi_tphy_wrcslat[freq][ch] = hdlr->tphy_wrlat_org[freq];
    }
#endif /* DDRCTL_EXT_SBECC_AND_CRC*/

    QDYN_CFG_MATRIX(ptr, dfi_tphy_rdcslat, ch, freq);

    QDYN_CFG_MATRIX(ptr, dfi_tphy_wrcslat, ch, freq);

#ifdef DDRCTL_LPDDR
    QDYN.dfi_twck_delay[freq][ch] = PRE_CFG.dfi_twck_delay[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_delay, ch, freq);
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for tmgcfg
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_TMGCFG(uint32_t freq)
{
#ifdef MEMC_PROG_FREQ_RATIO_EN
    uint32_t reset_value = REGB_FREQ_CH0(freq).tmgcfg.value;
    uint32_t value = 0;

    SNPS_WRITE_FIELD(value, TMGCFG_FREQUENCY_RATIO, ddrctl_sw_get_ratio(CFG, freq));
    REGB_FREQ_CH0(freq).tmgcfg.value = value;
    if ((CINIT_REG_FORCE_WRITE == 1) || (reset_value != value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, 0) + TMGCFG, value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, 1) + TMGCFG, value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
#endif /* MEMC_PROG_FREQ_RATIO_EN */
}

/**
 * @brief function to setup the register field values for dfitmg4
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    dwc_ddrctl_cinit_lpddr54_prgm_REGB_FREQ_DFITMG4(freq,ch);
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG4(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dfitmg5
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG5(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    dwc_ddrctl_cinit_lpddr54_prgm_REGB_FREQ_DFITMG5(freq,ch);
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG5(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dfitmg6
 */
#ifdef MEMC_LPDDR5X
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG6(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    dwc_ddrctl_cinit_lpddr54_prgm_REGB_FREQ_DFITMG6(freq,ch);
    SNPS_TRACE("Leaving");
}
#else /* MEMC_LPDDR5X */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG6(uint32_t freq, uint32_t ch)
{
};
#endif /* MEMC_LPDDR5X */

/**
 * @brief function to setup the register field values for rfshset1tmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg0,
        &REGB_FREQ_CH1(freq).rfshset1tmg0
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_LPDDR
    if (IS_LPDDR4) {
        DYN.t_refi_x1_x32[freq][ch] = (STATIC.per_bank_refresh & !STATIC.per_bank_refresh_opt_en) ? timing->lpddr4_trfipb : timing->lpddr4_trfiab;
        DYN.t_refi_x1_x32[freq][ch] = DYN.t_refi_x1_x32[freq][ch] / SPD.tck_ps[freq];
        DYN.t_refi_x1_x32[freq][ch] = (DYN.t_refi_x1_sel[freq][ch]) ? DYN.t_refi_x1_x32[freq][ch] : DIV_32(DYN.t_refi_x1_x32[freq][ch]);
    } else if (IS_LPDDR5) {
        uint32_t tck = SPD.tck_ps[freq];
        uint32_t trefi_ps = (STATIC.per_bank_refresh & !STATIC.per_bank_refresh_opt_en) ? timing->lpddr5_trefipb_ps : timing->lpddr5_trefi_ps;

        tck = (DYN.t_refi_x1_sel[freq][ch]) ? tck : tck * 32;
        DYN.t_refi_x1_x32[freq][ch] = DIVIDE_ROUNDDOWN(trefi_ps, tck);
    }


    if (IS_LPDDR5 || IS_LPDDR4) {
        if (DYN.derate_enable) {
            if (DYN.t_refi_x1_sel[freq][ch])
                CONSTRAIN_MAX(DYN.refresh_margin[freq][ch], (DYN.t_refi_x1_x32[freq][ch] >> 7) - 1);
            else
                CONSTRAIN_MAX(DYN.refresh_margin[freq][ch], (DYN.t_refi_x1_x32[freq][ch] >> 2) - 1);
        } else {
            // no de-rating dcheck
            SNPS_LOG("p = %u, ch = %u, DYN.refresh_margin = %u, t_refi_x1_x32 = %u, max = %u", freq, ch, DYN.refresh_margin[freq][ch], DYN.t_refi_x1_x32[freq][ch], (DYN.t_refi_x1_x32[freq][ch] >> 1) - 1);
            if (DYN.t_refi_x1_sel[freq][ch])
                CONSTRAIN_MAX(DYN.refresh_margin[freq][ch], (DYN.t_refi_x1_x32[freq][ch] >> 5) - 1);
            else
                CONSTRAIN_MAX(DYN.refresh_margin[freq][ch], ((DYN.t_refi_x1_x32[freq][ch] >> 1) - 1));
        }
    }
    if (IS_LPDDR5 && !STATIC.fixed_crit_refpb_bank_en) {
        if(DYN.refresh_to_x1_sel[freq][ch] && ((PRE_CFG.t_ras_min[freq][ch] + PRE_CFG.t_rp[freq][ch]) > 0x3F)) { // max value of refresh_to_x1_x32
            DYN.refresh_to_x1_sel[freq][ch] = 0;
        }
        if(DYN.refresh_to_x1_sel[freq][ch]) {
            if(DYN.refresh_to_x1_x32[freq][ch] < PRE_CFG.t_ras_min[freq][ch] + PRE_CFG.t_rp[freq][ch]) {
                //Override the refresh_to_x1_x32 value to avoid refresh timeout error.
                DYN.refresh_to_x1_x32[freq][ch] = PRE_CFG.t_ras_min[freq][ch] + PRE_CFG.t_rp[freq][ch] + 1;
            }
        } else {
            if(DYN.refresh_to_x1_x32[freq][ch]*32 < PRE_CFG.t_ras_min[freq][ch] + PRE_CFG.t_rp[freq][ch]) {
                //Override the refresh_to_x1_x32 value to avoid refresh timeout error.
                DYN.refresh_to_x1_x32[freq][ch] = ((PRE_CFG.t_ras_min[freq][ch] + PRE_CFG.t_rp[freq][ch])/32) + 1;
            }
        }
    }
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
    if (IS_DDR5) {
        uint32_t t_refi = DIV_32(timing->ddr5_trefi1_ps / SPD.tck_ps[freq]);
        DYN.t_refi_x1_x32[freq][ch] =t_refi;   // set tREFI1 always
    } else if (IS_DDR4) {
        uint32_t t_refi = DIV_32(timing->ddr4_trefi_ps / SPD.tck_ps[freq]);
        if (DDR4_MR[freq].mr4.refresh_mode==1 &&
            DDR4_MR[freq].mr4.refresh_range==1 ) {
            DYN.t_refi_x1_x32[freq][ch] = DIV_2(t_refi);
        } else {
            DYN.t_refi_x1_x32[freq][ch] = (QDYN.fgr_mode == 2) ? DIV_4(t_refi) : ((QDYN.fgr_mode == 1) ? DIV_2(t_refi) : t_refi);
        }
    }
#endif /* DDRCTL_DDR */

    DYN_CFG_MATRIX(ptr, t_refi_x1_x32, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_margin, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_to_x1_x32, ch, freq);

#ifdef DDRCTL_LPDDR
    DYN_CFG_MATRIX(ptr, t_refi_x1_sel, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_to_x1_sel, ch, freq);
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for rfshset1tmg1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg1,
        &REGB_FREQ_CH1(freq).rfshset1tmg1
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4)
        DYN.t_rfc_min[freq][ch] = CEIL(timing->ddr4_trfc_min_fgr_ps, SPD.tck_ps[freq]);
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5)
        DYN.t_rfc_min[freq][ch] = CEIL(timing->ddr5_trfc_fgr_ps, SPD.tck_ps[freq]);
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        if (STATIC.per_bank_refresh)
            DYN.t_rfc_min[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfcpb, SPD.tck_ps[freq]);
        else
            DYN.t_rfc_min[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfcab, SPD.tck_ps[freq]);

        DYN.t_rfc_min_ab[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfcab, SPD.tck_ps[freq]);
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        if (STATIC.per_bank_refresh)
            DYN.t_rfc_min[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfcpb_ps, SPD.tck_ps[freq]);
        else
            DYN.t_rfc_min[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfcab_ps, SPD.tck_ps[freq]);

        DYN.t_rfc_min_ab[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfcab_ps, SPD.tck_ps[freq]);
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    DYN_CFG_MATRIX(ptr, t_rfc_min, ch, freq);
    DYN_CFG_MATRIX(ptr, t_rfc_min_ab, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for rfshset1tmg2
 */
#ifdef MEMC_LPDDR4_OR_UMCTL2_CID_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg2,
        &REGB_FREQ_CH1(freq).rfshset1tmg2
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_LPDDR
    DYN.t_pbr2act[freq][ch] = PRE_CFG.t_pbr2act[freq][ch];
    DYN_CFG_MATRIX(ptr, t_pbr2act, ch, freq);

    DYN.t_pbr2pbr[freq][ch] = PRE_CFG.t_pbr2pbr[freq][ch];
    DYN_CFG_MATRIX(ptr, t_pbr2pbr, ch, freq);
#endif /* DDRCTL_LPDDR */

#ifdef UMCTL2_CID_EN
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
#ifdef CINIT_DDR4
    if (IS_DDR4)
        DYN.t_rfc_min_dlr[freq][ch] = CEIL(timing->ddr4_trfc_dlr_fgr_ps, SPD.tck_ps[freq]);
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5)
        DYN.t_rfc_min_dlr[freq][ch] = CEIL(timing->ddr5_trfc_dlr_fgr_ps, SPD.tck_ps[freq]);
#endif /* CINIT_DDR5 */

    // CONSTRAIN_INSIDE includes the endpoints, i.e., range is [min, max]. The t_rfc_min_dlr_2 field is 10 bits which is
    // a maximum value of 1023.
    CONSTRAIN_MAX(DYN.t_rfc_min_dlr[freq][ch], 1023);

    DYN_CFG_MATRIX(ptr, t_rfc_min_dlr, ch, freq);
#endif /* UMCTL2_CID_EN */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* MEMC_LPDDR4_OR_UMCTL2_CID_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG2(uint32_t freq, uint32_t ch)
{
};
#endif /* MEMC_LPDDR4_OR_UMCTL2_CID_EN */

/**
 * @brief function to setup the register field values for rfshset1tmg3
 */
#ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg3,
        &REGB_FREQ_CH1(freq).rfshset1tmg3
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef DDRCTL_DDR
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

    DYN.t_rfcsb[freq][ch] = CEIL(timing->ddr5_trfcsb_ps, SPD.tck_ps[freq]);
    DYN_CFG_MATRIX(ptr, t_rfcsb, ch, freq);

    DYN.t_refsbrd[freq][ch] = CEIL(timing->ddr5_trefsbrd_ps, SPD.tck_ps[freq]);
    DYN_CFG_MATRIX(ptr, t_refsbrd, ch, freq);
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
    DYN_CFG_MATRIX(ptr, refresh_to_ab_x32, ch, freq);
#endif /* DDRCTL_LPDDR */
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else  /* DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG3(uint32_t freq, uint32_t ch)
{
};
#endif  /* DDRCTL_DDR_OR_MEMC_LPDDR4 */

/**
 * @brief function to setup the register field values for rfshset1tmg4
 */
#ifdef MEMC_NUM_RANKS_GT_1
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG4_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg4,
        &REGB_FREQ_CH1(freq).rfshset1tmg4
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_MATRIX(ptr, refresh_timer1_start_value_x32, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_timer0_start_value_x32, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG4, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NUM_RANKS_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG4(uint32_t freq, uint32_t ch)
{
};
#endif /* MEMC_NUM_RANKS_GT_1 */

/**
 * @brief function to setup the register field values for rfshset1tmg5
 */
#ifdef MEMC_NUM_RANKS_GT_2
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG5(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG5_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg5,
        &REGB_FREQ_CH1(freq).rfshset1tmg5
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_MATRIX(ptr, refresh_timer2_start_value_x32, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_timer3_start_value_x32, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG5, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NUM_RANKS_GT_2 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG5(uint32_t freq, uint32_t ch)
{
};
#endif /* MEMC_NUM_RANKS_GT_2 */

/**
 * @brief function to setup the register field values for rfshset1tmg6
 */
#ifdef UMCTL2_CID_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG6(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG6_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg6,
        &REGB_FREQ_CH1(freq).rfshset1tmg6
    };
    uint32_t tmp = ptr[ch]->value;

    CONSTRAIN_MAX(STATIC.refresh_timer_lr_offset_x32[freq][ch], 2047);
    STATIC_CFG_MATRIX(ptr, refresh_timer_lr_offset_x32, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG6, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_CID_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG6(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_CID_EN */

/**
 * @brief function to setup the register field values for rfshset1tmg7
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_CID_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG7(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG7_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg7,
        &REGB_FREQ_CH1(freq).rfshset1tmg7
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_refsbrd_dlr[freq][ch] = PRE_CFG.t_refsbrd_dlr[freq][ch];
    DYN_CFG_MATRIX(ptr, t_refsbrd_dlr, ch, freq);

    DYN.t_rfcsb_dlr[freq][ch] = PRE_CFG.t_rfcsb_dlr[freq][ch];
    DYN_CFG_MATRIX(ptr, t_rfcsb_dlr, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG7, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_CID_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG7(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && UMCTL2_CID_EN */

/**
 * @brief function to setup the register field values for rfshset1tmg8
 */
#ifdef UMCTL2_HET_RANK_RFC
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG8(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG8_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg8,
        &REGB_FREQ_CH1(freq).rfshset1tmg8
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_MATRIX(ptr, t_rfc_min_het, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG8, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HET_RANK_RFC */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG8(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_HET_RANK_RFC */

#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG9(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG9_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg9,
        &REGB_FREQ_CH1(freq).rfshset1tmg9
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.refab_hi_sch_gap[freq][ch] = PRE_CFG.refab_hi_sch_gap[freq][ch];
    DYN_CFG_MATRIX(ptr, refab_hi_sch_gap, ch, freq);

    DYN.refsb_hi_sch_gap[freq][ch] = PRE_CFG.refsb_hi_sch_gap[freq][ch];
    DYN_CFG_MATRIX(ptr, refsb_hi_sch_gap, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG9, ptr[ch]->value);

    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG9(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG10(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG10_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg10,
        &REGB_FREQ_CH1(freq).rfshset1tmg10
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef CINIT_DDR5
    QDYN.t_win_size_1xtrefi[freq][ch] = CEIL(timing->ddr5_trefi1_ps, 32 * SPD.tck_ps[freq]);
    QDYN_CFG_MATRIX(ptr, t_win_size_1xtrefi, ch, freq);
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG10, ptr[ch]->value);
    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG10(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for rfshset1tmg11
 */
#ifdef DDRCTL_LPDDR_MIXED_PKG 
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG11(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG11_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg11,
        &REGB_FREQ_CH1(freq).rfshset1tmg11
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_pbr2pbr_mp[freq][ch] = PRE_CFG.t_pbr2pbr_mp[freq][ch];
    DYN_CFG_MATRIX(ptr, t_pbr2pbr_mp, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG11, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR_MIXED_PKG  */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG11(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR_MIXED_PKG  */

/**
 * @brief function to setup the register field values for rfshset1tmg12
 */
#ifdef DDRCTL_LPDDR_MIXED_PKG 
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG12(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET1TMG12_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset1tmg12,
        &REGB_FREQ_CH1(freq).rfshset1tmg12
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        if (STATIC.per_bank_refresh)
            DYN.t_rfc_min_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfcpb_mp, SPD.tck_ps[freq]);
        else
            DYN.t_rfc_min_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfcab_mp, SPD.tck_ps[freq]);

        DYN.t_rfc_min_ab_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfcab_mp, SPD.tck_ps[freq]);
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        if (STATIC.per_bank_refresh)
            DYN.t_rfc_min_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfcpb_mp_ps, SPD.tck_ps[freq]);
        else
            DYN.t_rfc_min_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfcab_mp_ps, SPD.tck_ps[freq]);

        DYN.t_rfc_min_ab_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfcab_mp_ps, SPD.tck_ps[freq]);
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    DYN_CFG_MATRIX(ptr, t_rfc_min_mp, ch, freq);
    DYN_CFG_MATRIX(ptr, t_rfc_min_ab_mp, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET1TMG12, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR_MIXED_PKG  */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG12(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR_MIXED_PKG  */

#ifdef DDRCTL_LPDDR_RFM
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFMSET1TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFMSET1TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfmset1tmg0,
        &REGB_FREQ_CH1(freq).rfmset1tmg0
    };
    uint32_t tmp = ptr[ch]->value;

    if(IS_LPDDR5) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
        QDYN.t_rfmpb[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfmpb_ps, SPD.tck_ps[freq]);
    } else {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
        QDYN.t_rfmpb[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfmpb, SPD.tck_ps[freq]);
    }

    QDYN_CFG_MATRIX(ptr, t_rfmpb, ch, freq);

    if (tmp != ptr[ch]->value)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFMSET1TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_LPDDR_RFM */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFMSET1TMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR_RFM */

#if defined(DDRCTL_LPDDR_RFM) && defined(DDRCTL_LPDDR_MIXED_PKG)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFMSET1TMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFMSET1TMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfmset1tmg1,
        &REGB_FREQ_CH1(freq).rfmset1tmg1
    };
    uint32_t tmp = ptr[ch]->value;

    if(IS_LPDDR5) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
        QDYN.t_rfmpb_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr5_trfmpb_mp_ps, SPD.tck_ps[freq]);
    } else {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
        QDYN.t_rfmpb_mp[freq][ch] = cinit_ps_to_tck(timing->lpddr4_trfmpb_mp, SPD.tck_ps[freq]);
    }

    QDYN_CFG_MATRIX(ptr, t_rfmpb_mp, ch, freq);

    if (tmp != ptr[ch]->value)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFMSET1TMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_LPDDR_RFM && DDRCTL_LPDDR_MIXED_PKG */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFMSET1TMG1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR_RFM && DDRCTL_LPDDR_MIXED_PKG */

#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_ECSSET1TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    ECSSET1TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).ecsset1tmg0,
        &REGB_FREQ_CH1(freq).ecsset1tmg0
    };
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

        //See Automatic ECS COS for details on calculation of t_refi_ecs_offset_x1_x32
        uint32_t l_auto_ecs_expected_ref;
        uint32_t l_shortened_t_refi_ps;
        uint32_t l_offset_ps;
        uint32_t l_offset_x1_x32;
        uint32_t l_t_refi_ps = timing->ddr5_trefi1_ps;
        uint32_t l_t_ecs_int_ps = QDYN.t_ecs_int_x1024[freq][ch] * 1024 * SPD.tck_ps[freq];
        uint32_t l_refresh_burst = DYN.refresh_burst;

        //Calculate number of refreshes expected to happen within tECSint and ROUNDUP
        l_auto_ecs_expected_ref = (l_t_ecs_int_ps / l_t_refi_ps) + (l_t_ecs_int_ps % l_t_refi_ps != 0);

        //+ 1 is for Auto ECS REFab
        l_shortened_t_refi_ps = l_t_ecs_int_ps / (l_auto_ecs_expected_ref + l_refresh_burst + 1);
        l_offset_ps = l_t_refi_ps - l_shortened_t_refi_ps;
        //Note - This reg field will always be x32 for DDR5
        l_offset_x1_x32 = l_offset_ps / (32 * SPD.tck_ps[freq]);
        //l_offset can reduce to 0 under certain tck_ps/refresh_burst condition, make min 1 in these cases
        if (l_offset_x1_x32 == 0) {
                l_offset_x1_x32 = 1;
        }
        DYN.t_refi_ecs_offset_x1_x32[freq][ch] = l_offset_x1_x32;

        SNPS_LOG("QDYN.t_ecs_int_x1024[freq][ch]:%u", QDYN.t_ecs_int_x1024[freq][ch]);
        SNPS_LOG("l_t_ecs_int_ps:%u", l_t_ecs_int_ps);
        SNPS_LOG("l_refresh_burst:%u", l_refresh_burst);
        SNPS_LOG("(l_t_ecs_int_ps / l_t_refi_ps):%u", (l_t_ecs_int_ps / l_t_refi_ps));
        SNPS_LOG("(l_t_ecs_int_ps % l_t_refi_ps != 0):%u", (l_t_ecs_int_ps % l_t_refi_ps != 0));
        SNPS_LOG("l_auto_ecs_expected_ref:%u", l_auto_ecs_expected_ref);
        SNPS_LOG("l_shortened_t_refi_ps:%u", l_shortened_t_refi_ps);
        SNPS_LOG("l_offset_ps:%u", l_offset_ps);
        SNPS_LOG("l_offset_x1_x32:%u", l_offset_x1_x32);
    }

#endif
    QDYN_CFG_MATRIX(ptr, t_ecs_int_x1024, ch, freq);

    DYN_CFG_MATRIX(ptr, t_refi_ecs_offset_x1_x32, ch, freq);

    dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + ECSSET1TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_ECSSET1TMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for zqset1tmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET1TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    ZQSET1TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).zqset1tmg0,
        &REGB_FREQ_CH1(freq).zqset1tmg0
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        STATIC.t_zq_short_nop[freq][ch] = timing->lpddr4_tzqcs;
        STATIC.t_zq_long_nop[freq][ch] = timing->lpddr4_tzqcl;
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        STATIC.t_zq_short_nop[freq][ch] = cinit_ps_to_tck(timing->lpddr5_tzqlat_ps, SPD.tck_ps[freq]);
        // 1) Bug 8603: Add a margin of 10 cycles to account for internal DUT delays
        /// @todo Add dfi_t_ctrlup_max to t_zq_long_nopw workaround until Bug 10298 is resolved in RTL.
        //  NOTE: dfi_t_ctrlup_max only exists for FREQ0
        // 2) P80001562-304066: STATIC.dfi_t_ctrlup_max may be too long because of PPT2.
        // Workaround doesn't need to consider PPT2 latency so setting t_ctrlup_max_default (see dwc_ddrctl_cinit_lpddr54_dfi_timings.c) directly instead of dfi_t_ctrlup_max.
        STATIC.t_zq_long_nop[freq][ch] = CEIL(timing->lpddr5_tzqcal_ps, SPD.tck_ps[freq]) + 10 + (28 + hdlr->phy_timing_params.pipe_dfi_misc) /*+ STATIC.dfi_t_ctrlup_max[ch]*/ ;
        SNPS_WARN("Setting t_zq_long_nop to t_zq_long_nop + STATIC.dfi_t_ctrlup_max (%u) as a workaround for bug 10298", STATIC.t_zq_long_nop[freq][ch]);
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        STATIC.t_zq_short_nop[freq][ch] = timing->ddr4_tzqcs_tck;
        STATIC.t_zq_long_nop[freq][ch] = timing->ddr4_tzqoper_tck;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        STATIC.t_zq_short_nop[freq][ch] = cinit_ps_to_tck(timing->ddr5_tzqlat_ps, SPD.tck_ps[freq]);
        STATIC.t_zq_long_nop[freq][ch] = CEIL(timing->ddr5_tzqcal_ps, SPD.tck_ps[freq]);
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

    STATIC_CFG_MATRIX(ptr, t_zq_short_nop, ch, freq);

    STATIC_CFG_MATRIX(ptr, t_zq_long_nop, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + ZQSET1TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for zqset1tmg1
 */
#ifdef DDRCTL_DDR4_OR_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET1TMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    ZQSET1TMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).zqset1tmg1,
        &REGB_FREQ_CH1(freq).zqset1tmg1
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_LPDDR
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4)
        STATIC.t_zq_reset_nop[freq][ch] = timing->lpddr4_tzqreset;
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5)
        STATIC.t_zq_reset_nop[freq][ch] = cinit_ps_to_tck(timing->lpddr5_tzqreset_ps, SPD.tck_ps[freq]);
#endif /* CINIT_LPDDR5 */
    STATIC_CFG_MATRIX(ptr, t_zq_reset_nop, ch, freq);
#endif /* MEMC_LPDDR4 */

    STATIC_CFG_MATRIX(ptr, t_zq_short_interval_x1024, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + ZQSET1TMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET1TMG1(uint32_t freq, uint32_t ch)
{
}
#endif

/**
 * @brief function to setup the register field values for pwrtmg
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_PWRTMG(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    PWRTMG_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).pwrtmg,
        &REGB_FREQ_CH1(freq).pwrtmg
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, selfref_to_x32, ch, freq);

    QDYN_CFG_MATRIX(ptr, powerdown_to_x32, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + PWRTMG, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for schedtmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_SCHEDTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    SCHEDTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).schedtmg0,
        &REGB_FREQ_CH1(freq).schedtmg0
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC_CFG_MATRIX(ptr, rdwr_idle_gap, ch, freq);

    STATIC_CFG_MATRIX(ptr, pageclose_timer, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + SCHEDTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for perflpr1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_PERFLPR1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    PERFLPR1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).perflpr1,
        &REGB_FREQ_CH1(freq).perflpr1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, lpr_xact_run_length, ch, freq);

    QDYN_CFG_MATRIX(ptr, lpr_max_starve, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + PERFLPR1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for hwlptmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_HWLPTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    HWLPTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).hwlptmg0,
        &REGB_FREQ_CH1(freq).hwlptmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, hw_lp_idle_x32, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + HWLPTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dvfsctl0
 */
#if defined(UMCTL2_HWFFC_EN) && defined(DDRCTL_LPDDR)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DVFSCTL0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DVFSCTL0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dvfsctl0,
        &REGB_FREQ_CH1(freq).dvfsctl0
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC_CFG_MATRIX(ptr, dvfsq_enable, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DVFSCTL0, ptr[ch]->value);
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DVFSCTL0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for derateval0
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEVAL0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DERATEVAL0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).derateval0,
        &REGB_FREQ_CH1(freq).derateval0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.derated_t_rcd[freq][ch] = PRE_CFG.derated_t_rcd[freq][ch];
    QDYN_CFG_MATRIX(ptr, derated_t_rcd, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->derated_t_rcd, 1, 0xff);    // cannot be zerom 8bits

    QDYN.derated_t_ras_min[freq][ch] = PRE_CFG.derated_t_ras_min[freq][ch];
    QDYN_CFG_MATRIX(ptr, derated_t_ras_min, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->derated_t_ras_min, 1, 0xff);    // cannot be zerom 8bits

    QDYN.derated_t_rp[freq][ch] = PRE_CFG.derated_t_rp[freq][ch];
    QDYN_CFG_MATRIX(ptr, derated_t_rp, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->derated_t_rp, 1, 0x7f);    // cannot be zerom 7bits

    QDYN.derated_t_rrd[freq][ch] = PRE_CFG.derated_t_rrd[freq][ch];
    QDYN_CFG_MATRIX(ptr, derated_t_rrd, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->derated_t_rrd, 1, 0x3f);    // cannot be zerom 6bits

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DERATEVAL0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEVAL0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for derateval1
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEVAL1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DERATEVAL1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).derateval1,
        &REGB_FREQ_CH1(freq).derateval1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.derated_t_rc[freq][ch] = PRE_CFG.derated_t_rc[freq][ch];
    QDYN_CFG_MATRIX(ptr, derated_t_rc, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->derated_t_rc, 1, 0xff);    // cannot be zerom 8bits

#ifdef MEMC_LPDDR5X
    if (SPD.use_lpddr5x && IS_LPDDR5) {
    QDYN.derated_t_rcd_write[freq][ch] = PRE_CFG.derated_t_rcd_write[freq][ch];
    QDYN_CFG_MATRIX(ptr, derated_t_rcd_write, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->derated_t_rcd_write, 1, 0xff);    // cannot be zero, 8 bits
    }
#endif  /*MEMC_LPDDR5X*/

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DERATEVAL1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEVAL1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for DFIMSGTMG0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIMSGTMG0(void)
{
#ifdef DDRCTL_DFI_CTRLMSG
    DFIMSGTMG0_t *const ptr = &REGB_FREQ_CH0(0).dfimsgtmg0;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dfi_t_ctrlmsg_resp);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 0) + DFIMSGTMG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 1) + DFIMSGTMG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
#endif /* DDRCTL_DFI_CTRLMSG */
}


/**
 * @brief function to setup the register field values for derateint
 */
#ifdef MEMC_LPDDR2
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEINT(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DERATEINT_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).derateint,
        &REGB_FREQ_CH1(freq).derateint
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, mr4_read_interval, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->mr4_read_interval, 1);    // cannot be zero

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DERATEINT, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* MEMC_LPDDR2 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEINT(uint32_t freq, uint32_t ch)
{
};
#endif /* MEMC_LPDDR2 */

/**
 * @brief function to setup the register field values for ranktmg0
 */
#if defined(DDRCTL_DDR4_OR_LPDDR) && defined(UMCTL2_NUM_LRANKS_TOTAL_GT_1)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANKTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RANKTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).ranktmg0,
        &REGB_FREQ_CH1(freq).ranktmg0
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
#ifdef MEMC_NUM_RANKS_GT_1
#ifdef DDRCTL_LPDDR
    uint32_t wr_gap_min, rd_gap_min;
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        wr_gap_min = PRE_CFG.odtloff[freq][ch] - PRE_CFG.odtlon[freq][ch] - 8 + 1;
        rd_gap_min = 4 + hdlr->memCtrlr_m.lpddr4_mr[freq].mr1.rd_postamble;

        // dcheck if min is being violated.
        // then overwrite with min
        if (wr_gap_min > QDYN.diff_rank_wr_gap[freq][ch]) {
            SNPS_LOG("%u: attempt to set diff_rank_wr_gap = %u less than min", freq, QDYN.diff_rank_wr_gap[freq][ch]);
            QDYN.diff_rank_wr_gap[freq][ch] = wr_gap_min;
        }
        if (rd_gap_min > QDYN.diff_rank_rd_gap[freq][ch])
            QDYN.diff_rank_rd_gap[freq][ch] = rd_gap_min;
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.dq_odt > 0) {    //DQ ODT ON
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1 
               if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.nt_odt && hdlr->memCtrlr_m.lpddr5_mr[freq].mr41.nt_dq_odt>0 ) {        // WCK_ON = 1 && DQ ODT && NT ODT && ENHANCED NT_ODT
                   QDYN.diff_rank_wr_gap[freq][ch] = PRE_CFG.diff_rank_wr_gap_wck_on_dq_odt_nt_odt[freq][ch];
                   QDYN.diff_rank_rd_gap[freq][ch] = PRE_CFG.diff_rank_rd_gap_wck_on_dq_odt_nt_odt[freq][ch];
               } else {            // WCK_ON = 1 && DQ_ODT
                   QDYN.diff_rank_wr_gap[freq][ch] = PRE_CFG.diff_rank_wr_gap_wck_on_odt[freq][ch];
                   QDYN.diff_rank_rd_gap[freq][ch] = PRE_CFG.diff_rank_rd_gap_wck_on_odt[freq][ch];
               }
            } else {            // WCK_ON = 0 && DQ ODT
                QDYN.diff_rank_wr_gap[freq][ch] = PRE_CFG.diff_rank_wr_gap_odt[freq][ch];
                QDYN.diff_rank_rd_gap[freq][ch] = PRE_CFG.diff_rank_rd_gap_odt[freq][ch];
            }
        } else {                // ODT OFF
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1
                QDYN.diff_rank_wr_gap[freq][ch] = PRE_CFG.diff_rank_wr_gap_wck_on[freq][ch];
                QDYN.diff_rank_rd_gap[freq][ch] = PRE_CFG.diff_rank_rd_gap_wck_on[freq][ch];
            } else {            // WCK_ON = 0
                QDYN.diff_rank_wr_gap[freq][ch] = PRE_CFG.diff_rank_wr_gap[freq][ch];
                QDYN.diff_rank_rd_gap[freq][ch] = PRE_CFG.diff_rank_rd_gap[freq][ch];
            }
        }
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    /// @todo write constraint for diff_rank_rd_gap DDR4/5
    /// @todo write constraint for diff_rank_rd_gap LPDDR5

    QDYN_CFG_MATRIX(ptr, diff_rank_rd_gap, ch, freq);

    QDYN_CFG_MATRIX(ptr, diff_rank_wr_gap, ch, freq);

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        CONSTRAIN_INSIDE(ptr[ch]->diff_rank_rd_gap, 3, 15);
        CONSTRAIN_INSIDE(ptr[ch]->diff_rank_wr_gap, wr_gap_min, 15);
    }
#endif
#endif /* DDRCTL_LPDDR */

#endif /* MEMC_NUM_RANKS_GT_1 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANKTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_NUM_LRANKS_TOTAL_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANKTMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_1 */

/**
 * @brief function to setup the register field values for initmr0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    INITMR0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).initmr0,
        &REGB_FREQ_CH1(freq).initmr0
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[freq];

        QDYN.mr[freq][ch] = ((mregs->mr0.wr_recovery >> 3) & 0x00000001) << 13;        // mr0[15:12]
        QDYN.mr[freq][ch] |= ((mregs->mr0.cl >> 4) & 0x00000001) << 12;            // mr0[15:12]
        QDYN.mr[freq][ch] |= (mregs->mr0.wr_recovery & 0x00000007) << 9;        // mr0_wr_recovery mr0[11:9]
        QDYN.mr[freq][ch] |= (mregs->mr0.dll_reset & 0x00000001) << 8;            // mr0[8] :DLL Reset
        QDYN.mr[freq][ch] |= 0;                                // mr0[7] :TM = 0
        QDYN.mr[freq][ch] |= ((mregs->mr0.cl >> 1) & 0x00000007) << 4;            // mr0_cl[3:1] mr0[6:4]
        QDYN.mr[freq][ch] |= (mregs->mr0.burst_type & 0x00000001) << 3;            // mr0_burst_type mr0[3:3]
        QDYN.mr[freq][ch] |= (mregs->mr0.cl & 0x00000001) << 2;                // mr0_cl[0] mr0[2:2]
        QDYN.mr[freq][ch] |= mregs->mr0.burst_length & 0x00000003;            // mr0_burst_length mr0[1:0]

        QDYN.emr[freq][ch] = 0;                                // mr1[15:11]
        QDYN.emr[freq][ch] |= (mregs->mr1.rtt_nom & 0x00000007) << 8;            // mr1_rtt[2:0] mr1[10:8]
        QDYN.emr[freq][ch] |= 0;                            // mr1[7:5]
        QDYN.emr[freq][ch] |= (mregs->mr1.al & 0x00000003) << 3;            // mr1_al mr1[4:3]
        QDYN.emr[freq][ch] |= (mregs->mr1.output_driver_impedance & 0x00000003) << 1;    // mr1_output_driver_impedance mr1[2:1]
        QDYN.emr[freq][ch] |= mregs->mr1.dll_enable & 0x00000001;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        // dont care
        QDYN.mr[freq][ch] = 0;

        QDYN.emr[freq][ch] = 0;
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        lpddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr4_mr[freq];

        mregs->mr1.wr_preamble = 1;    // required

        //To configure MR1 of LPDDR4
        QDYN.mr[freq][ch] = 0;                                // mr1[15:8]
        QDYN.mr[freq][ch] |= (mregs->mr1.rd_postamble & 0x00000001) << 7;        // mr1[7]
        QDYN.mr[freq][ch] |= (mregs->mr1.wr_recovery & 0x00000007) << 4;        // mr1[6:4]
        QDYN.mr[freq][ch] |= (mregs->mr1.rd_preamble & 0x00000001) << 3;        // mr1[3]
        QDYN.mr[freq][ch] |= (mregs->mr1.wr_preamble & 0x00000001) << 2;        // mr1[2]
        QDYN.mr[freq][ch] |= mregs->mr1.burst_length & 0x00000003;            // mr1[1:0]

        //To configure MR2 of LPDDR4
        QDYN.emr[freq][ch] = 0;                                // mr2[15:7]
        QDYN.emr[freq][ch] |= (mregs->mr2.wls & 0x00000001) << 6;            // mr2[6]
        QDYN.emr[freq][ch] |= mregs->mr2.rl_wl & 0x0000003f;                // mr2[5:0]
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        // dont care
        QDYN.mr[freq][ch] = 0;

        QDYN.emr[freq][ch] = 0;
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    QDYN_CFG_MATRIX(ptr, mr, ch, freq);

    QDYN_CFG_MATRIX(ptr, emr, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + INITMR0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for initmr1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    INITMR1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).initmr1,
        &REGB_FREQ_CH1(freq).initmr1
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        RFSHMOD1_t * const ptr2 = &REGB_DDRC_CH0.rfshmod1;
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[freq];

        QDYN.emr2[freq][ch] = 0;                            // mr2[15:13]
        QDYN.emr2[freq][ch] |= (mregs->mr2.write_crc & 0x00000001) << 12;        // mr2[12]
        QDYN.emr2[freq][ch] |= (mregs->mr2.rtt_wr & 0x00000007) << 9;            // mr2[11:9]
        QDYN.emr2[freq][ch] |= 0;                            // mr2[8]
        QDYN.emr2[freq][ch] |= (mregs->mr2.auto_self_ref & 0x00000003) << 6;        // mr2[7:6]
        QDYN.emr2[freq][ch] |= (mregs->mr2.cwl & 0x00000007) << 3;            // mr2[5:3]
        QDYN.emr2[freq][ch] |= 0;                            // mr2[2:0]

        QDYN.emr3[freq][ch] = 0;                            // mr3[15:11]
        QDYN.emr3[freq][ch] |= (mregs->mr3.wcl & 0x00000003) << 9;            // mr3[10:9]
        QDYN.emr3[freq][ch] |= (ptr2->fgr_mode & 0x00000003) << 6;            // mr3[8:6]
        QDYN.emr3[freq][ch] |= 0;                            // mr3[5:4]
        QDYN.emr3[freq][ch] |= (mregs->mr3.geardown & 0x00000003) << 3;            // mr3[3]
        QDYN.emr3[freq][ch] |= 0;                            // mr3[2:0]
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        // dont care
        QDYN.emr2[freq][ch] = 0;

        QDYN.emr3[freq][ch] = 0;
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        INITTMG0_t * const ptr2 = &REGB_DDRC_CH0.inittmg0;
        lpddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr4_mr[freq];

        CONSTRAIN_EQ(mregs->mr3.write_dbi, QDYN.wr_dbi_en[0]);
        CONSTRAIN_EQ(mregs->mr3.read_dbi, QDYN.rd_dbi_en[0]);

        //To configure MR3 of LPDDR4
        QDYN.emr2[freq][ch] = 0;                            // mr3[15:8]
        QDYN.emr2[freq][ch] |= (mregs->mr3.write_dbi & 0x00000001) << 7;        // mr3[7] : DBI-WR
        QDYN.emr2[freq][ch] |= (mregs->mr3.read_dbi & 0x00000001) << 6;            // mr3[6] : DBI-RD
        QDYN.emr2[freq][ch] |= 0;                            // mr3[5:3] : PDDS
        QDYN.emr2[freq][ch] |= 0;                            // mr3[2] : RFU
        QDYN.emr2[freq][ch] |= (mregs->mr3.wr_postamble & 0x00000001) << 1;        // mr3[1] : WR-PST
        QDYN.emr2[freq][ch] |= mregs->mr3.pu_cal & 0x00000001;                // mr3[0] : PU-CA

        //To configure MR13 of LPDDR4
        QDYN.emr3[freq][ch] = 0;                            // mr13[15:8]
        QDYN.emr3[freq][ch] |= (mregs->mr13.fsp_op & 0x00000001) << 7;            // mr13[7] : FSP-OP
        QDYN.emr3[freq][ch] |= (mregs->mr13.fsp_wr & 0x00000001) << 6;            // mr13[6] : FSP-WR
        QDYN.emr3[freq][ch] |= (mregs->mr13.dmd & 0x00000001) << 5;            // mr13[5] : DMD
        QDYN.emr3[freq][ch] |= 0;                            // mr13[4]
        QDYN.emr3[freq][ch] |= ((ptr2->skip_dram_init >> 1) & 0x00000001) << 3;        // mr13[3]
        QDYN.emr3[freq][ch] |= 0;                            // mr13[2:0]
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.emr2[freq][ch] = 0;
        QDYN.emr3[freq][ch] = 0;
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    QDYN_CFG_MATRIX(ptr, emr2, ch, freq);

    QDYN_CFG_MATRIX(ptr, emr3, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + INITMR1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for initmr2
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    INITMR2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).initmr2,
        &REGB_FREQ_CH1(freq).initmr2
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[freq];

        QDYN.mr4[freq][ch] = 0;                                // mr4[15:13]
        QDYN.mr4[freq][ch] |= (mregs->mr4.wr_preamble & 0x00000001) << 12;        // mr4[12]
        QDYN.mr4[freq][ch] |= (mregs->mr4.rd_preamble & 0x00000001) << 11;        // mr4[11]
        QDYN.mr4[freq][ch] |= 0;                            // mr4[10]
        QDYN.mr4[freq][ch] |= (mregs->mr4.selfref_abort & 0x00000001) << 9;        // mr4[9]
        QDYN.mr4[freq][ch] |= (mregs->mr4.cal & 0x00000003) << 6;            // mr4[8:6]
        QDYN.mr4[freq][ch] |= 0;                            // mr4[4]
        QDYN.mr4[freq][ch] |= (mregs->mr4.refresh_mode  & 0x00000001) << 3;        // mr4[3]
        QDYN.mr4[freq][ch] |= (mregs->mr4.refresh_range & 0x00000001) << 2;        // mr4[2]
        QDYN.mr4[freq][ch] |= 0;                            // mr4[1:0]

        QDYN.mr5[freq][ch] = 0;                                // mr5[15:13]
        QDYN.mr5[freq][ch] |= (mregs->mr5.read_dbi & 0x00000001) << 12;            // mr5[12]
        QDYN.mr5[freq][ch] |= (mregs->mr5.write_dbi & 0x00000001) << 11;        // mr5[11]
        QDYN.mr5[freq][ch] |= (mregs->mr5.data_mask & 0x00000001) << 10;        // mr5[10]
        QDYN.mr5[freq][ch] |= (mregs->mr5.ca_parity_persistent & 0x00000001) << 9;    // mr5[9]
        QDYN.mr5[freq][ch] |= (mregs->mr5.rtt_park & 0x00000007) << 6;            // mr5[8:6]
        QDYN.mr5[freq][ch] |= (mregs->mr5.dis_odt_input_buf_in_pd & 0x00000001) << 5;    // mr5[5]
        QDYN.mr5[freq][ch] |= 0;                            // mr4[4:3]
        QDYN.mr5[freq][ch] |= mregs->mr5.parity_latency_mode & 0x00000007;        // mr5[2:0]
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN.mr4[freq][ch] = 0;
        QDYN.mr5[freq][ch] = 0;
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        lpddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr4_mr[freq];

        QDYN.mr4[freq][ch] = 0;                                // mr11[15:8]
        QDYN.mr4[freq][ch] |= 0;                            // mr11[7] RFU
        QDYN.mr4[freq][ch] |= (mregs->mr11.ca_odt & 0x00000007) << 4;            // mr11[6:4] TUF
        QDYN.mr4[freq][ch] |= 0;                            // mr11[3] RFU
        QDYN.mr4[freq][ch] |= mregs->mr11.dq_odt & 0x00000007;                // mr11[2:0] DQ ODT

        QDYN.mr5[freq][ch] = 0;                                // mr12[15:7]
        QDYN.mr5[freq][ch] |= (mregs->mr12.vr_ca & 0x00000001) << 6;            // mr12[6] VR-CA
        QDYN.mr5[freq][ch] |= mregs->mr12.vref_ca & 0x0000003f;                // mr12[5:0] VR-CA
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        QDYN.mr4[freq][ch] = 0;
        QDYN.mr5[freq][ch] = 0;
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    QDYN_CFG_MATRIX(ptr, mr4, ch, freq);

    QDYN_CFG_MATRIX(ptr, mr5, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + INITMR2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for initmr3
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    INITMR3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).initmr3,
        &REGB_FREQ_CH1(freq).initmr3
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_DDR
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[freq];

        QDYN.mr6[freq][ch] = 0;                                // mr6[15:13]
        QDYN.mr6[freq][ch] |= (mregs->mr6.tccd_l & 0x00000007) << 10;            // mr6[12]

        QDYN.mr22[freq][ch] = 0;
    } else if (IS_DDR5) {
        QDYN.mr6[freq][ch] = 0;

        QDYN.mr22[freq][ch] = 0;
    }
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        lpddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr4_mr[freq];

        QDYN.mr6[freq][ch] = 0;                                // mr14[15:8]
        QDYN.mr6[freq][ch] |= 0;                            // mr14[7] RFU
        QDYN.mr6[freq][ch] |= (mregs->mr14.vr_dq & 0x00000001) << 6;            // mr14[6] VR(DQ)
        QDYN.mr6[freq][ch] |= mregs->mr14.vref_dq & 0x0000003f;                // mr14[5:0] VREF(DQ)

        QDYN.mr22[freq][ch] = 0;                            // mr22[15:8] : not used
        QDYN.mr22[freq][ch] |= (mregs->mr22.odtd & 0x00000003) << 6;            // mr22[7:6] : ODTD for x8_2ch(byte) mode
        QDYN.mr22[freq][ch] |= (mregs->mr22.odtd_ca & 0x00000001) << 5;            // mr22[5] : ODTD-CA
        QDYN.mr22[freq][ch] |= (mregs->mr22.odtd_cs & 0x00000001) << 4;            // mr22[4] : ODTD-CS
        QDYN.mr22[freq][ch] |= (mregs->mr22.odtd_ck & 0x00000001) << 3;            // mr22[3] : ODTD-CK
        QDYN.mr22[freq][ch] |= mregs->mr22.soc_odt & 0x00000007;            // mr22[3] : SOC ODTD
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        // dont care
        QDYN.mr6[freq][ch] = 0;

        QDYN.mr22[freq][ch] = 0;

#ifdef MEMC_LINK_ECC
        lpddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr5_mr[freq];

        QDYN.mr22[freq][ch] = 0;                            // mr22[15:8] : not used
        QDYN.mr22[freq][ch] |= (mregs->mr22.recc & 0x00000003) << 6;            // mr22[ 7:6] : Read link ECC
        QDYN.mr22[freq][ch] |= (mregs->mr22.wecc & 0x00000003) << 4;            // mr22[ 5:4] : Writr link ECC
        QDYN.mr22[freq][ch] |= 0;                            // mr22[ 3:0] : not used
#endif /* MEMC_LINK_ECC */
    }
#endif  // CINIT_LPDDR5
    QDYN_CFG_MATRIX(ptr, mr22, ch, freq);
#endif /* DDRCTL_LPDDR */

    QDYN_CFG_MATRIX(ptr, mr6, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + INITMR3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dramset2tmg0
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg0,
        &REGB_FREQ_CH1(freq).dramset2tmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.wr2pre_2[freq][ch] = PRE_CFG.wr2pre_2[freq][ch];

    QDYN_CFG_MATRIX(ptr, wr2pre_2, ch, freq);

    QDYN.t_faw_2[freq][ch] = PRE_CFG.tfaw_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_faw_2, ch, freq);

    QDYN.t_ras_min_2[freq][ch] = PRE_CFG.t_ras_min_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ras_min_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg1
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg1,
        &REGB_FREQ_CH1(freq).dramset2tmg1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.rd2pre_2[freq][ch] = PRE_CFG.rd2pre_2[freq][ch];

    QDYN_CFG_MATRIX(ptr, rd2pre_2, ch, freq);

    QDYN.t_rc_2[freq][ch] = PRE_CFG.t_rc_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rc_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg2
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg2,
        &REGB_FREQ_CH1(freq).dramset2tmg2
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.rd2wr_2[freq][ch] = PRE_CFG.rd2wr_2[freq][ch];

    QDYN_CFG_MATRIX(ptr, rd2wr_2, ch, freq);
    CONSTRAIN_INSIDE(ptr[ch]->rd2wr_2, 0, 255);    // 8 bits

    QDYN.wr2rd_2[freq][ch] = PRE_CFG.wr2rd_2[freq][ch];

    QDYN_CFG_MATRIX(ptr, wr2rd_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG2(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg3
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg3,
        &REGB_FREQ_CH1(freq).dramset2tmg3
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_mr_2[freq][ch] = PRE_CFG.t_mr_2[freq][ch];

    QDYN_CFG_MATRIX(ptr, t_mr_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG3(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg4
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG4_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg4,
        &REGB_FREQ_CH1(freq).dramset2tmg4
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_rcd_2[freq][ch] = PRE_CFG.t_rcd_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rcd_2, ch, freq);
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        CONSTRAIN_INSIDE(ptr[ch]->t_rcd_2, 1, 0x7f);    // cannot be zero, 7 bits
    }
#endif
    QDYN.t_rrd_2[freq][ch] = PRE_CFG.t_rrd_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rrd_2, ch, freq);

    QDYN.t_rp_2[freq][ch] = PRE_CFG.t_rp_2[freq][ch];

    if(IS_DDR4) {
    QDYN.t_rp_2[freq][ch] = QDYN.t_rp_2[freq][ch] + 1;  // @todo: tempfix for bugzilla 6578 - bug is marked fixed by
                                                        // using frequency to set clock period. It is NOT documented
                                                        // if the + 1 is still required
    }
    QDYN_CFG_MATRIX(ptr, t_rp_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG4, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG4(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg8
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG8(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG8_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg8,
        &REGB_FREQ_CH1(freq).dramset2tmg8
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_xs_dll_x32_2[freq][ch] = 0x44;    /// @todo finish t_xs_dll_x32 calculation
    QDYN_CFG_MATRIX(ptr, t_xs_dll_x32_2, ch, freq);

    QDYN.t_xs_x32_2[freq][ch] = PRE_CFG.t_xs_x32_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_xs_x32_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG8, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG8(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg9
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG9(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG9_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg9,
        &REGB_FREQ_CH1(freq).dramset2tmg9
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_rrd_s_2[freq][ch] = PRE_CFG.t_rrd_s_2[freq][ch];
    QDYN.wr2rd_s_2[freq][ch] = PRE_CFG.wr2rd_s_2[freq][ch];

    QDYN_CFG_MATRIX(ptr, t_rrd_s_2, ch, freq);
    QDYN_CFG_MATRIX(ptr, wr2rd_s_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG9, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG9(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg13
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG13(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG13_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg13,
        &REGB_FREQ_CH1(freq).dramset2tmg13
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ccd_w2_2[freq][ch] = PRE_CFG.t_ccd_w2_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w2_2, ch, freq);

    QDYN.t_ppd_2[freq][ch] = PRE_CFG.t_ppd_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ppd_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG13, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG13(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg16
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN) && defined(UMCTL2_CID_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG16(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG16_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg16,
        &REGB_FREQ_CH1(freq).dramset2tmg16
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ccd_dlr_2[freq][ch] = PRE_CFG.t_ccd_dlr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_dlr_2, ch, freq);

    QDYN.t_rrd_dlr_2[freq][ch] = PRE_CFG.t_rrd_dlr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rrd_dlr_2, ch, freq);

    QDYN.t_faw_dlr_2[freq][ch] = PRE_CFG.t_faw_dlr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_faw_dlr_2, ch, freq);

#ifdef DDRCTL_CAPAR_RETRY
    QDYN.t_rp_ca_parity_2[freq][ch] = 5; /// @todo dramset1tmg16 is missing this code and value also. The
                                         // 5 value is the register reset setting
    QDYN_CFG_MATRIX(ptr, t_rp_ca_parity_2, ch, freq);
#endif /* DDRCTL_CAPAR_RETRY */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG16, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN && UMCTL2_CID_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG16(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN && UMCTL2_CID_EN */

/**
 * @brief function to setup the register field values for dramset2tmg22
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG22(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG22_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg22,
        &REGB_FREQ_CH1(freq).dramset2tmg22
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_wr2rd_dpr_2[freq][ch] = PRE_CFG.t_wr2rd_dpr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr2rd_dpr_2, ch, freq);

    QDYN.t_rd2wr_dpr_2[freq][ch] = PRE_CFG.t_rd2wr_dpr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rd2wr_dpr_2, ch, freq);

#ifdef UMCTL2_CID_EN
    QDYN.t_wr2rd_dlr_2[freq][ch] = PRE_CFG.t_wr2rd_dlr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr2rd_dlr_2, ch, freq);

    QDYN.t_rd2wr_dlr_2[freq][ch] = PRE_CFG.t_rd2wr_dlr_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_rd2wr_dlr_2, ch, freq);
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG22, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG22(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg26
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG26(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG26_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg26,
        &REGB_FREQ_CH1(freq).dramset2tmg26
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_ccd_w_s_2[freq][ch] = PRE_CFG.t_ccd_w_s_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w_s_2, ch, freq);

    QDYN.t_ccd_r_s_2[freq][ch] = PRE_CFG.t_ccd_r_s_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_r_s_2, ch, freq);

    QDYN.t_ccd_w_2[freq][ch] = PRE_CFG.t_ccd_w_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w_2, ch, freq);

    QDYN.t_ccd_r_2[freq][ch] = PRE_CFG.t_ccd_r_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_r_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG26, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG26(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg27
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG27(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG27_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg27,
        &REGB_FREQ_CH1(freq).dramset2tmg27
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_mrr2mpc_2[freq][ch] = PRE_CFG.t_mrr2mpc_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_mrr2mpc_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG27, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG27(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for dramset2tmg31
 */
#if defined(DDRCTL_HW_RFM_CTRL) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG31(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET2TMG31_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg31,
        &REGB_FREQ_CH1(freq).dramset2tmg31
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, rfm_raaimt_2, ch, freq);

    QDYN_CFG_MATRIX(ptr, rfm_raa_thr_2, ch, freq);

    QDYN_CFG_MATRIX(ptr, rfm_raa_ref_decr_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG31, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_HW_RFM_CTRL && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG31(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_HW_RFM_CTRL && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for DRAMSET2TMG33
 */
#if defined(DDRCTL_DDR5CTL) && defined(DDRCTL_TWO_TIMING_SETS_EN) && defined(DDRCTL_DDR5CTL_HIGHSPEED)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG33(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DRAMSET1TMG33_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dramset2tmg33,
        &REGB_FREQ_CH1(freq).dramset2tmg33
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_wr2rd_m_2[freq][ch] = PRE_CFG.t_wr2rd_m_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr2rd_m_2, ch, freq);

    QDYN.t_ccd_w_m_2[freq][ch] = PRE_CFG.t_ccd_w_m_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_w_m_2, ch, freq);

    QDYN.t_ccd_r_m_2[freq][ch] = PRE_CFG.t_ccd_r_m_2[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_ccd_r_m_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DRAMSET2TMG33, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG33(uint32_t freq, uint32_t ch)
{
};
#endif
/**
 * @brief function to setup the register field values for mramtmg0
 */
#ifdef UMCTL2_DDR4_MRAM_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRAMTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).mramtmg0,
        &REGB_FREQ_CH1(freq).mramtmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_faw_mram, ch, freq);

#ifdef MEMC_NUM_TOTAL_BANKS_4
    CONSTRAIN_EQ(ptr[ch]->t_faw_mram, 0x1);    //In a 4-bank design, set this register to 0x1 independent of the frequency ratio mode.
#endif /* MEMC_NUM_TOTAL_BANKS_4 */

    QDYN_CFG_MATRIX(ptr, t_ras_min_mram, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + MRAMTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DDR4_MRAM_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_DDR4_MRAM_EN */

/**
 * @brief function to setup the register field values for mramtmg1
 */
#ifdef UMCTL2_DDR4_MRAM_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRAMTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).mramtmg1,
        &REGB_FREQ_CH1(freq).mramtmg1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_rc_mram, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + MRAMTMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DDR4_MRAM_EN */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG1(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_DDR4_MRAM_EN */

/**
 * @brief function to setup the register field values for mramtmg2
 */
#ifdef UMCTL2_DDR4_MRAM_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRAMTMG2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).mramtmg2,
        &REGB_FREQ_CH1(freq).mramtmg2
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_rcd_mram, ch, freq);

#ifdef MEMC_FREQ_RATIO_2
    CONSTRAIN_MIN(ptr[ch]->t_rcd_mram, 2);    //Minimum value allowed for this register is 2 when the controller is operating in 1:2 frequency ratio mode
#endif /* MEMC_FREQ_RATIO_2 */

    QDYN_CFG_MATRIX(ptr, t_rrd_mram, ch, freq);

    QDYN_CFG_MATRIX(ptr, t_rp_mram, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + MRAMTMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DDR4_MRAM_EN */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG2(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_DDR4_MRAM_EN */

/**
 * @brief function to setup the register field values for mramtmg3
 */
#ifdef UMCTL2_DDR4_MRAM_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRAMTMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).mramtmg3,
        &REGB_FREQ_CH1(freq).mramtmg3
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_rrd_s_mram, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + MRAMTMG3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DDR4_MRAM_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG3(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_DDR4_MRAM_EN */

/**
 * @brief function to setup the register field values for dfitmg3
 */
#if defined(DDRCTL_DDR4) && !defined(MEMC_CMD_RTN2IDLE)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg3,
        &REGB_FREQ_CH1(freq).dfitmg3
    };
    uint32_t tmp = ptr[ch]->value;

    // DDR5/4 PUB 3.40a
    // Table 5-7
    QDYN.dfi_t_geardown_delay[freq][ch] = 4 + CFG->phy_timing_params.pipe_dfi_misc;
    if (ddrctl_sw_get_ratio(CFG, freq) == DWC_RATIO_1_4) {
       QDYN.dfi_t_geardown_delay[freq][ch] = DIV_2(QDYN.dfi_t_geardown_delay[freq][ch]);
    }

    QDYN_CFG_MATRIX(ptr, dfi_t_geardown_delay, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_CMD_RTN2IDLE */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG3(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_CMD_RTN2IDLE */

/**
 * @brief function to setup the register field values for dfiupdtmg1
 */
#ifdef DDRCTL_DDR4_OR_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFIUPDTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfiupdtmg1,
        &REGB_FREQ_CH1(freq).dfiupdtmg1
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC_CFG_MATRIX(ptr, dfi_t_ctrlupd_interval_min_x1024, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->dfi_t_ctrlupd_interval_min_x1024, 0x1);

    STATIC_CFG_MATRIX(ptr, dfi_t_ctrlupd_interval_max_x1024, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->dfi_t_ctrlupd_interval_max_x1024, 0x1);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFIUPDTMG1, ptr[ch]->value);
    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG1(uint32_t freq, uint32_t ch)
{
};
#endif

static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG2(uint32_t freq)
{
#ifdef DDRCTL_PPT2
    DFIUPDTMG2_t *const ptr = &REGB_FREQ_CH0(freq).dfiupdtmg2;
    uint32_t tmp = ptr->value;

    ptr->dfi_t_ctrlupd_interval_type1 = DYN.dfi_t_ctrlupd_interval_type1[freq];

    ptr->ppt2_en                = DYN.ppt2_en[freq];
    ptr->ppt2_override          = STATIC.ppt2_override[freq];
    ptr->ctrlupd_after_dqsosc   = STATIC.ctrlupd_after_dqsosc[freq];

    ptr->dfi_t_ctrlupd_interval_type1_unit = DYN.dfi_t_ctrlupd_interval_type1_unit[freq];
    CONSTRAIN_MIN(ptr->dfi_t_ctrlupd_interval_type1_unit, 0x1);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 0) + DFIUPDTMG2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 1) + DFIUPDTMG2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
#endif
}

/**
 * @brief function to setup the register field values for dfiupdtmg1
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFIUPDTMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfiupdtmg3,
        &REGB_FREQ_CH1(freq).dfiupdtmg3
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];
    STATIC.dfi_t_ctrlupd_burst_interval_x8[freq][ch] = hdlr->phy_timing_params.dfi_t_ctrlupd_burst_interval_x8[freq] - DIV_8(QDYN.read_latency[freq][ch] + DIV_2(timing->burst_length));
    STATIC_CFG_MATRIX(ptr, dfi_t_ctrlupd_burst_interval_x8, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->dfi_t_ctrlupd_burst_interval_x8, 0x1);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFIUPDTMG3, ptr[ch]->value);
    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG3(uint32_t freq, uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for rcdinit1
 */
#if defined(UMCTL2_HWFFC_EN) && defined(DDRCTL_DDR)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RCDINIT1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rcdinit1,
        &REGB_FREQ_CH1(freq).rcdinit1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, ctrl_word_2, ch, freq);

    QDYN_CFG_MATRIX(ptr, ctrl_word_1, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RCDINIT1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HWFFC_EN && DDRCTL_DDR */
static inline  void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT1(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_HWFFC_EN && DDRCTL_DDR */

/**
 * @brief function to setup the register field values for rcdinit2
 */
#if defined(UMCTL2_HWFFC_EN) && defined(DDRCTL_DDR)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RCDINIT2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rcdinit2,
        &REGB_FREQ_CH1(freq).rcdinit2
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, ctrl_word_4, ch, freq);

    QDYN_CFG_MATRIX(ptr, ctrl_word_3, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RCDINIT2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HWFFC_EN && DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT2(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_HWFFC_EN && DDRCTL_DDR */

/**
 * @brief function to setup the register field values for rcdinit3
 */
#if defined(UMCTL2_HWFFC_EN) && defined(DDRCTL_DDR)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RCDINIT3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rcdinit3,
        &REGB_FREQ_CH1(freq).rcdinit3
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, ctrl_word_6, ch, freq);

    QDYN_CFG_MATRIX(ptr, ctrl_word_5, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RCDINIT3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HWFFC_EN) && DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT3(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_HWFFC_EN) && DDRCTL_DDR */

/**
 * @brief function to setup the register field values for rcdinit4
 */
#if defined(UMCTL2_HWFFC_EN) && defined(DDRCTL_DDR)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RCDINIT4_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rcdinit4,
        &REGB_FREQ_CH1(freq).rcdinit4
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, ctrl_word_8, ch, freq);

    QDYN_CFG_MATRIX(ptr, ctrl_word_7, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RCDINIT4, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HWFFC_EN && DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT4(uint32_t freq, uint32_t ch)
{
};
#endif /* UMCTL2_HWFFC_EN && DDRCTL_DDR */

/**
 * @brief function to setup the register field values for dqsoscctl0
 */
#ifdef LPDDR45_DQSOSC_EN
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DQSOSCCTL0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DQSOSCCTL0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dqsoscctl0,
        &REGB_FREQ_CH1(freq).dqsoscctl0
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_MATRIX(ptr, dqsosc_interval, ch, freq);

    DYN_CFG_MATRIX(ptr, dqsosc_interval_unit, ch, freq);

    DYN_CFG_MATRIX(ptr, dqsosc_enable, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* LPDDR45_DQSOSC_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DQSOSCCTL0(uint32_t freq, uint32_t ch)
{
};
#endif /* LPDDR45_DQSOSC_EN */

/**
 * @brief function to setup the register field values for ranktmg1
 */

static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RANKTMG1(uint32_t freq, uint32_t ch)
{
#if defined(DDRCTL_DDR4_OR_LPDDR) && defined(MEMC_NUM_RANKS_GT_1)
    RANKTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).ranktmg1,
        &REGB_FREQ_CH1(freq).ranktmg1
    };
    uint32_t tmp = ptr[ch]->value;

    if (IS_LPDDR5) {
#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR5
        if (hdlr->memCtrlr_m.lpddr5_mr[freq].mr11.dq_odt > 0) {    // ODT ON
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1
                QDYN.wr2rd_dr[freq][ch] = PRE_CFG.wr2rd_dr_wck_on_odt[freq][ch];
                QDYN.rd2wr_dr[freq][ch] = PRE_CFG.rd2wr_dr_wck_on_odt[freq][ch];
            } else {            // WCK_ON = 0
                QDYN.wr2rd_dr[freq][ch] = PRE_CFG.wr2rd_dr_odt[freq][ch];
                QDYN.rd2wr_dr[freq][ch] = PRE_CFG.rd2wr_dr_odt[freq][ch];
            }
        } else {                // ODT OFF
            if (QDYN.wck_on[ch] == 1) {    // WCK_ON = 1
                QDYN.wr2rd_dr[freq][ch] = PRE_CFG.wr2rd_dr_wck_on[freq][ch];
                QDYN.rd2wr_dr[freq][ch] = PRE_CFG.rd2wr_dr_wck_on[freq][ch];
            } else {            // WCK_ON = 0
                QDYN.wr2rd_dr[freq][ch] = PRE_CFG.wr2rd_dr[freq][ch];
                QDYN.rd2wr_dr[freq][ch] = PRE_CFG.rd2wr_dr[freq][ch];
            }
        }
#endif
#endif /* DDRCTL_LPDDR */
    } else{
        QDYN.wr2rd_dr[freq][ch] = PRE_CFG.wr2rd_dr[freq][ch];
        QDYN.rd2wr_dr[freq][ch] = PRE_CFG.rd2wr[freq][ch] + 5;
    }

    QDYN_CFG_MATRIX(ptr, wr2rd_dr, ch, freq);
    QDYN_CFG_MATRIX(ptr, rd2wr_dr, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RANKTMG1, ptr[ch]->value);
    }
#endif /* defined(DDRCTL_DDR4_OR_LPDDR) && defined(MEMC_NUM_RANKS_GT_1) */
}


/**
 * @brief function to setup the register field values for dfitmg7
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG7(uint32_t freq, uint32_t ch)
{
#ifdef DDRCTL_DFI_SB_WDT_OR_MEMC_DDR5
#ifdef DDRCTL_DDR
    dwc_ddrctl_cinit_ddr54_prgm_REGB_FREQ_DFITMG7(freq,ch);
#else /* DDRCTL_DDR */
    DFITMG7_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg7,
        &REGB_FREQ_CH1(freq).dfitmg7
    };
    uint32_t tmp = ptr[ch]->value;
    uint32_t ratio;
    uint32_t tck_ps = SPD.tck_ps[freq];

    ratio = ddrctl_sw_get_ratio_factor(CFG, freq);

#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
      QDYN.dfi_t_init_start[freq][ch] =  (tck_ps < 625)  ? ((ratio==4) ? 450 : 610) : /* > 3200 */
                                         (tck_ps < 1250) ? ((ratio==4) ? 410 : 540) : /* > 1600 */
                                                                               420;   /* <=1600 */

      QDYN_CFG_MATRIX(ptr, dfi_t_init_start, ch, freq);

      QDYN.dfi_t_init_complete[freq][ch] = (tck_ps < 625)  ? ((ratio==4) ? 3170 : 4640) : /* > 3200 */
                                           (tck_ps < 1250) ? ((ratio==4) ? 2570 : 3980) : /* > 1600 */
                                                                                  2970;   /* <=1600 */
      QDYN_CFG_MATRIX(ptr, dfi_t_init_complete, ch, freq);
    }
#endif /* CINIT_LPDDR4 */

#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
      QDYN.dfi_t_init_start[freq][ch] =  (tck_ps < 625)  ?  580 : /* > 3200 */
                                         (tck_ps < 1250) ?  580 : /* > 1600 */
                                                            469;  /* <=1600 */
      QDYN_CFG_MATRIX(ptr, dfi_t_init_start, ch, freq);

      QDYN.dfi_t_init_complete[freq][ch] = (tck_ps < 625)  ? 5640 : /* > 3200 */
                                           (tck_ps < 1250) ? 5440 : /* > 1600 */
                                                             4430;  /* <=1600 */
      QDYN_CFG_MATRIX(ptr, dfi_t_init_complete, ch, freq);
    }
#endif /* CINIT_LPDDR5 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
    dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG7, ptr[ch]->value);
#endif /* DDRCTL_DDR */
#endif /* DDRCTL_DFI_SB_WDT_OR_MEMC_DDR5 */
};


/**
 * @brief function to setup the register field values for rfshset2tmg0
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg0,
        &REGB_FREQ_CH1(freq).rfshset2tmg0
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_refi_x1_x32_2[freq][ch] = PRE_CFG.t_refi_x1_x32_2[freq][ch];

    DYN_CFG_MATRIX(ptr, t_refi_x1_x32_2, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_margin_2, ch, freq);

    DYN_CFG_MATRIX(ptr, refresh_to_x1_x32_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for rfshset2tmg1
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg1,
        &REGB_FREQ_CH1(freq).rfshset2tmg1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_rfc_min_2[freq][ch] = PRE_CFG.t_rfc_min_2[freq][ch];

    DYN_CFG_MATRIX(ptr, t_rfc_min_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for rfshset2tmg2
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN) && defined(UMCTL2_CID_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG2(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG2_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg2,
        &REGB_FREQ_CH1(freq).rfshset2tmg2
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_rfc_min_dlr_2[freq][ch] = PRE_CFG.t_rfc_min_dlr_2[freq][ch];
    // CONSTRAIN_INSIDE includes the endpoints, i.e., range is [min, max]. The t_rfc_min_dlr_2 field is 10 bits which is
    // a maximum value of 1023.
    CONSTRAIN_INSIDE(DYN.t_rfc_min_dlr_2[freq][ch], 0, 1023);

    DYN_CFG_MATRIX(ptr, t_rfc_min_dlr_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN && UMCTL2_CID_EN*/
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG2(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN && UMCTL2_CID_EN*/

/**
 * @brief function to setup the register field values for rfshset2tmg3
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG3(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG3_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg3,
        &REGB_FREQ_CH1(freq).rfshset2tmg3
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_rfcsb_2[freq][ch] = PRE_CFG.t_rfcsb_2[freq][ch];
    DYN_CFG_MATRIX(ptr, t_rfcsb_2, ch, freq);

    DYN.t_refsbrd_2[freq][ch] = PRE_CFG.t_refsbrd_2[freq][ch];
    DYN_CFG_MATRIX(ptr, t_refsbrd_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG3, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG3(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for rfshset2tmg6
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN) && defined(UMCTL2_CID_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG6(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG6_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg6,
        &REGB_FREQ_CH1(freq).rfshset2tmg6
    };
    uint32_t tmp = ptr[ch]->value;

    CONSTRAIN_INSIDE(STATIC.refresh_timer_lr_offset_x32_2[freq][ch], 0, 2047);
    STATIC_CFG_MATRIX(ptr, refresh_timer_lr_offset_x32_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG6, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN && UMCTL2_CID_EN*/
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG6(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN && UMCTL2_CID_EN*/

/**
 * @brief function to setup the register field values for rfshset2tmg7
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN) && defined(UMCTL2_CID_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG7(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG7_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg7,
        &REGB_FREQ_CH1(freq).rfshset2tmg7
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.t_refsbrd_dlr_2[freq][ch] = PRE_CFG.t_refsbrd_dlr_2[freq][ch];
    DYN_CFG_MATRIX(ptr, t_refsbrd_dlr_2, ch, freq);

    DYN.t_rfcsb_dlr_2[freq][ch] = PRE_CFG.t_rfcsb_dlr_2[freq][ch];
    DYN_CFG_MATRIX(ptr, t_rfcsb_dlr_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG7, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_CID_EN && UMCTL2_CID_EN*/
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG7(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && UMCTL2_CID_EN && UMCTL2_CID_EN*/

#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG9(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG9_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg9,
        &REGB_FREQ_CH1(freq).rfshset2tmg9
    };
    uint32_t tmp = ptr[ch]->value;

    DYN.refab_hi_sch_gap_2[freq][ch] = PRE_CFG.refab_hi_sch_gap_2[freq][ch];
    DYN_CFG_MATRIX(ptr, refab_hi_sch_gap_2, ch, freq);

    DYN.refsb_hi_sch_gap_2[freq][ch] = PRE_CFG.refsb_hi_sch_gap_2[freq][ch];
    DYN_CFG_MATRIX(ptr, refsb_hi_sch_gap_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG9, ptr[ch]->value);

    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG9(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG10(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RFSHSET2TMG10_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).rfshset2tmg10,
        &REGB_FREQ_CH1(freq).rfshset2tmg10
    };
    uint32_t tmp = ptr[ch]->value;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][DDRCTL_CINIT_MAX_DEV_NUM-1];

#ifdef CINIT_DDR5
    QDYN.t_win_size_1xtrefi_2[freq][ch] = CEIL(timing->ddr5_trefi1_ps, 32 * SPD.tck_ps[freq]);
    QDYN_CFG_MATRIX(ptr, t_win_size_1xtrefi_2, ch, freq);
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RFSHSET2TMG10, ptr[ch]->value);
    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG10(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_ECSSET2TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    ECSSET2TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).ecsset2tmg0,
        &REGB_FREQ_CH1(freq).ecsset2tmg0
    };
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[freq][0];

        //See Automatic ECS COS for details on calculation of t_refi_ecs_offset_x1_x32
        uint32_t l_auto_ecs_expected_ref;
        uint32_t l_shortened_t_refi_ps;
        uint32_t l_offset_ps;
        uint32_t l_offset_x1_x32;
        uint32_t l_t_refi_ps = timing->ddr5_trefi1_ps;
        uint32_t l_t_ecs_int_ps = QDYN.t_ecs_int_x1024_2[freq][ch] * 1024 * SPD.tck_ps[freq];
        uint32_t l_refresh_burst = DYN.refresh_burst;

        //Calculate number of refreshes expected to happen within tECSint and ROUNDUP
        l_auto_ecs_expected_ref = (l_t_ecs_int_ps / l_t_refi_ps) + (l_t_ecs_int_ps % l_t_refi_ps != 0);

        l_shortened_t_refi_ps = l_t_ecs_int_ps / (l_auto_ecs_expected_ref + l_refresh_burst + 1);
        l_offset_ps = l_t_refi_ps - l_shortened_t_refi_ps;
        //Note - This reg field will always be x32 for DDR5
        l_offset_x1_x32 = l_offset_ps / (32 * SPD.tck_ps[freq]);
        //l_offset can reduce to 0 under certain tck_ps/refresh_burst condition, make min 1 in these cases
        if (l_offset_x1_x32 == 0) {
                l_offset_x1_x32 = 1;
        }
        DYN.t_refi_ecs_offset_x1_x32_2[freq][ch] = l_offset_x1_x32;
    }
#endif  // CINIT_DDR5

    QDYN_CFG_MATRIX(ptr, t_ecs_int_x1024_2, ch, freq);

    DYN_CFG_MATRIX(ptr, t_refi_ecs_offset_x1_x32_2, ch, freq);

    dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + ECSSET2TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
};
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_ECSSET2TMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for zqset2tmg0
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_TWO_TIMING_SETS_EN)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET2TMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    ZQSET2TMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).zqset2tmg0,
        &REGB_FREQ_CH1(freq).zqset2tmg0
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC.t_zq_short_nop_2[freq][ch] = PRE_CFG.t_zq_short_nop_2[freq][ch];
    STATIC_CFG_MATRIX(ptr, t_zq_short_nop_2, ch, freq);

    STATIC.t_zq_long_nop_2[freq][ch] = PRE_CFG.t_zq_long_nop_2[freq][ch];
    STATIC_CFG_MATRIX(ptr, t_zq_long_nop_2, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + ZQSET2TMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET2TMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_TWO_TIMING_SETS_EN */

/**
 * @brief function to setup the register field values for odtcfg
 */
#ifdef DDRCTL_DDR4
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_ODTCFG(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    ODTCFG_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).odtcfg,
        &REGB_FREQ_CH1(freq).odtcfg
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef CINIT_DDR4
    uint32_t wr_preamble = (hdlr->memCtrlr_m.ddr4_mr[freq].mr4.wr_preamble==1) ? 2 : 1;
    uint32_t rd_preamble = (hdlr->memCtrlr_m.ddr4_mr[freq].mr4.rd_preamble==1) ? 2 : 1;
    uint32_t rd_odt_hold_unadjusted;

    QDYN.wr_odt_hold[freq][ch] = 5 + wr_preamble + QDYN.wr_crc_enable;
#ifndef MEMC_CMD_RTN2IDLE
    // make sure wr_odt_hold is even when geardown is enabled.
    if (QDYN.geardown_mode[ch] && (QDYN.wr_odt_hold[freq][ch] % 2))
        QDYN.wr_odt_hold[freq][ch] = QDYN.wr_odt_hold[freq][ch] - 1;
#endif // MEMC_CMD_RTN2IDLE

    QDYN.wr_odt_delay[freq][ch] =  QDYN.dfi_t_cmd_lat[freq][ch];
    // make sure wr_odt_delay is even when geardown is enabled.
    if (QDYN.geardown_mode[ch] && (QDYN.wr_odt_delay[freq][ch] % 2))
        QDYN.wr_odt_delay[freq][ch] = QDYN.wr_odt_delay[freq][ch] - 1;

    if( (QDYN.dfi_t_cmd_lat[freq][ch] + PRE_CFG.cl[freq] - PRE_CFG.cwl_x[freq]) < (rd_preamble - wr_preamble))
        QDYN.rd_odt_delay[freq][ch] = 0;
    else
        QDYN.rd_odt_delay[freq][ch] =  QDYN.dfi_t_cmd_lat[freq][ch] + PRE_CFG.cl[freq] - PRE_CFG.cwl_x[freq]
        - (rd_preamble - wr_preamble);

    rd_odt_hold_unadjusted = QDYN.rd_odt_delay[freq][ch];
#ifndef MEMC_CMD_RTN2IDLE
    // make sure rd_odt_delay is even when geardown is enabled.
    if (QDYN.geardown_mode[ch] && (QDYN.rd_odt_delay[freq][ch] % 2))
        QDYN.rd_odt_delay[freq][ch] = QDYN.rd_odt_delay[freq][ch] - 1;
#endif // MEMC_CMD_RTN2IDLE


    QDYN.rd_odt_hold[freq][ch] = 5 + rd_preamble - (QDYN.rd_odt_delay[freq][ch] - rd_odt_hold_unadjusted);
#ifndef MEMC_CMD_RTN2IDLE
    // make sure rd_odt_hold is even when geardown is enabled.
    if (QDYN.geardown_mode[ch] && (QDYN.rd_odt_hold[freq][ch] % 2))
        QDYN.rd_odt_hold[freq][ch] = QDYN.rd_odt_hold[freq][ch] - 1;
#endif // MEMC_CMD_RTN2IDLE


    QDYN_CFG_MATRIX(ptr, wr_odt_hold, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->wr_odt_hold, 0x2);

    QDYN_CFG_MATRIX(ptr, wr_odt_delay, ch, freq);

    QDYN_CFG_MATRIX(ptr, rd_odt_hold, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->rd_odt_hold, 0x2);

    QDYN_CFG_MATRIX(ptr, rd_odt_delay, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + ODTCFG, ptr[ch]->value);
#endif // CINIT_DDR4

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_ODTCFG(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for crcpartmg0
 */
#if defined(DDRCTL_DDR)
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_CRCPARTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    CRCPARTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).crcpartmg0,
        &REGB_FREQ_CH1(freq).crcpartmg0
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_MATRIX(ptr, t_wr_crc_alert_pw_min, ch, freq);

    DYN_CFG_MATRIX(ptr, t_wr_crc_alert_pw_max, ch, freq);
    CONSTRAIN_MIN(ptr[ch]->t_wr_crc_alert_pw_max, (ptr[ch]->t_wr_crc_alert_pw_min));

    SNPS_LOG("crcpartmg0[%d] = 0x%x", ch, ptr[ch]->value);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + CRCPARTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_CRCPARTMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for crcpartmg1
 */
#ifdef DDRCTL_CA_PARITY
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_CRCPARTMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    CRCPARTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).crcpartmg1,
        &REGB_FREQ_CH1(freq).crcpartmg1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_csalt[freq][ch] = PRE_CFG.t_csalt[freq][ch];

    QDYN_CFG_MATRIX(ptr, t_csalt, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + CRCPARTMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_CA_PARITY */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_CRCPARTMG1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_CA_PARITY */

#ifdef DDRCTL_WR_CRC_RETRY
void dwc_ddrctl_cinit_prgm_REGB_FREQ_RETRYTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RETRYTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).retrytmg0,
        &REGB_FREQ_CH1(freq).retrytmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.t_wr_crc_retry_window[freq][ch] = PRE_CFG.t_wr_crc_retry_window[freq][ch];
    QDYN_CFG_MATRIX(ptr, t_wr_crc_retry_window, ch, freq);

#ifdef DDRCTL_CAPAR_RETRY
    if (STATIC.capar_retry_enable[ch]) {
        QDYN.capar_retry_window[freq][ch] = PRE_CFG.capar_retry_window[freq][ch];
    } else {
        QDYN.capar_retry_window[freq][ch] = 0;
    }

    QDYN_CFG_MATRIX(ptr, capar_retry_window, ch, freq);
#endif /* DDRCTL_CAPAR_RETRY */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RETRYTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_WR_CRC_RETRY */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RETRYTMG0(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_WR_CRC_RETRY */

#ifdef DDRCTL_CAPAR_RETRY
/**
 * @brief function to setup the register field values for retrytmg1
 */
void dwc_ddrctl_cinit_prgm_REGB_FREQ_RETRYTMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    RETRYTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).retrytmg1,
        &REGB_FREQ_CH1(freq).retrytmg1
    };
    uint32_t tmp = ptr[ch]->value;

    if (STATIC.capar_retry_enable[ch]) {
        QDYN.retry_add_rd_lat_en[freq][ch] = PRE_CFG.retry_add_rd_lat_en[freq][ch];
        QDYN.retry_add_rd_lat[freq][ch] = PRE_CFG.retry_add_rd_lat[freq][ch];
    } else {
        QDYN.retry_add_rd_lat_en[freq][ch] = 0;
        QDYN.retry_add_rd_lat[freq][ch] = 0;
    }
    if (STATIC.capar_retry_enable[ch]) {
        QDYN.extra_rd_retry_window[freq][ch] = PRE_CFG.extra_rd_retry_window[freq][ch];
    } else {
        QDYN.extra_rd_retry_window[freq][ch] = 0;
    }

    QDYN_CFG_MATRIX(ptr, retry_add_rd_lat_en, ch, freq);
    QDYN_CFG_MATRIX(ptr, retry_add_rd_lat, ch, freq);
    QDYN_CFG_MATRIX(ptr, extra_rd_retry_window, ch, freq);

    dwc_ddrctl_cinit_common_prgm_REGB_FREQ_RETRYTMG1(freq,ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + RETRYTMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_CAPAR_RETRY */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_RETRYTMG1(uint32_t freq, uint32_t ch)
{
};
#endif /* DDRCTL_CAPAR_RETRY */

/**
 * @brief function to setup the register field values for perfhpr1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_PERFHPR1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    PERFHPR1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).perfhpr1,
        &REGB_FREQ_CH1(freq).perfhpr1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, hpr_xact_run_length, ch, freq);

    QDYN_CFG_MATRIX(ptr, hpr_max_starve, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + PERFHPR1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for perfwr1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_PERFWR1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    PERFWR1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).perfwr1,
        &REGB_FREQ_CH1(freq).perfwr1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, w_xact_run_length, ch, freq);

    QDYN_CFG_MATRIX(ptr, w_max_starve, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + PERFWR1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dfilptmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFILPTMG0(void)
{
    DFILPTMG0_t *const ptr = &REGB_FREQ_CH0(0).dfilptmg0;
    uint32_t tmp = ptr->value;

#ifdef DDRCTL_DDR
    STATIC_CFG(ptr, dfi_lp_wakeup_mpsm);
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
    STATIC_CFG(ptr, dfi_lp_wakeup_dsm);
#endif /* DDRCTL_LPDDR */

    STATIC_CFG(ptr, dfi_lp_wakeup_sr);

    STATIC_CFG(ptr, dfi_lp_wakeup_pd);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 0) + DFILPTMG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 1) + DFILPTMG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
}

/**
 * @brief function to setup the register field values for dfilptmg1
 */
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DFILPTMG1(void)
{
    DFILPTMG1_t *const ptr = &REGB_FREQ_CH0(0).dfilptmg1;

    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dfi_lp_wakeup_data);

    STATIC.dfi_tlp_resp = hdlr->phy_timing_params.dfi_tlp_resp;
    STATIC_CFG(ptr, dfi_tlp_resp);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 0) + DFILPTMG1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, 1) + DFILPTMG1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
}

#ifdef DDRCTL_LPDDR5_PPR_OR_DDRCTL_DDR4_PPR
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DDR4PPRTMG0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DDR4PPRTMG0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).ddr4pprtmg0,
        &REGB_FREQ_CH1(freq).ddr4pprtmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_pgm_x1_x1024, ch, freq);
    QDYN_CFG_MATRIX(ptr, t_pgm_x1_sel, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DDR4PPRTMG0, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

static void dwc_ddrctl_cinit_prgm_REGB_FREQ_DDR4PPRTMG1(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DDR4PPRTMG1_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).ddr4pprtmg1,
        &REGB_FREQ_CH1(freq).ddr4pprtmg1
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, t_pgmpst_x32, ch, freq);
    QDYN_CFG_MATRIX(ptr, t_pgm_exit, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DDR4PPRTMG1, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DDR4PPRTMG0(uint32_t freq, uint32_t ch)
{
}

static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_DDR4PPRTMG1(uint32_t freq, uint32_t ch)
{
}
#endif

/**
 * @brief function to setup the register field values for lnkeccctl0
 */
#ifdef MEMC_LINK_ECC
static void dwc_ddrctl_cinit_prgm_REGB_FREQ_LNKECCCTL0(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    LNKECCCTL0_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).lnkeccctl0,
        &REGB_FREQ_CH1(freq).lnkeccctl0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_MATRIX(ptr, rd_link_ecc_enable, ch, freq);

    QDYN_CFG_MATRIX(ptr, wr_link_ecc_enable, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + LNKECCCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_LINK_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_FREQ_LNKECCCTL0(uint32_t freq, uint32_t ch)
{
};
#endif /* MEMC_LINK_ECC */

/**
 * @brief iterate through all FREQ registers setting up a 32-bit value to
 * be programmed into each writable register.
 */
void dwc_ddrctl_cinit_prgm_REGB_FREQ(void)
{
    dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG0();
    dwc_ddrctl_cinit_prgm_REGB_FREQ_DFILPTMG0();
    dwc_ddrctl_cinit_prgm_REGB_FREQ_DFILPTMG1();
    dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIMSGTMG0();

    for (uint32_t freq = 0; freq < hdlr->num_pstates; freq++) {
        dwc_ddrctl_cinit_prgm_REGB_FREQ_TMGCFG(freq);
        dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG2(freq);
        for (uint32_t ch = 0; ch < hdlr->num_dch; ch++) {
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG4(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG5(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG6(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG7(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG8(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG9(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG10(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG12(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG13(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG14(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG16(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG17(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG18(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG20(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG21(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG22(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG24(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG25(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG26(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG27(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG30(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG31(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG32(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG33(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG34(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG35(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG36(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG37(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG38(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL4(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANK_SWITCH_TIMING_CONTROL5(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG4(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG5(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG6(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG10(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG11(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG12(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET1TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET1TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_PWRTMG(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_PERFLPR1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_HWLPTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DVFSCTL0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEVAL0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEVAL1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DERATEINT(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANKTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG4(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG5(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG6(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_INITMR3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG11(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG15(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG23(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG28(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET1TMG29(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG4(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG8(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG9(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG13(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG16(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG22(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG26(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG27(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG31(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DRAMSET2TMG33(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_SCHEDTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_MRAMTMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFIUPDTMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RCDINIT4(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DQSOSCCTL0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RANKTMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_ODTCFG(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_CRCPARTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_CRCPARTMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_PERFHPR1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_PERFWR1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DFITMG7(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG7(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG8(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET1TMG9(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFMSET1TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFMSET1TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_ECSSET1TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG2(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG3(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG6(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG7(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG9(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RFSHSET2TMG10(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_ECSSET2TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_ZQSET2TMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RETRYTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_RETRYTMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DDR4PPRTMG0(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_DDR4PPRTMG1(freq, ch);
            dwc_ddrctl_cinit_prgm_REGB_FREQ_LNKECCCTL0(freq, ch);
        }
    }
}

#undef DWC_USE_SET1_FOR_SET2_TMG
