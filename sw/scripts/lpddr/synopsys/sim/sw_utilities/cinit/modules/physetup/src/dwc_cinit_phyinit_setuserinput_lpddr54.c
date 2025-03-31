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
#include "dwc_ddrctl_cinit_defines.h"

#ifdef DDRCTL_LPDDR

#if PHYINIT == 0
#define DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE 4
#endif


/** @brief Function to call function need when configuring PHYINIT.
 * The follow steps are taken:
 * - calculate some local variables to map to PHYINT requirements.
 * - Setup userInputBasic
 * - Setup userInputAdvanced
 * - Setup userInputSim
 */
void dwc_cinit_phyinit_setuserinput(SubsysHdlr_t *cinit_cfg) {
    uint8_t train_2d;
    uint32_t num_dbyte, dram_type, dimm_type, cs_present_cha, cs_present_chb, enabled_dq_cha,
            enabled_dq_chb, dfi_mode, pllbypass, freqThreshold, freqThreshold_pllbypass;
    uint8_t temp_freq_ratio;
    uint32_t tmp_num_pstates;
    uint32_t num_active_dbyte_dfi0, num_active_dbyte_dfi1;
    uint32_t num_ch, num_dbytes_per_ch, num_rank, cfg_pstates, first_pstate;
    uint32_t mr1[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr2[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr3[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr11[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr12[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr13[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr14[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr22[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // Extra DDR5 MR Registers
    uint32_t mr10[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr15[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr16[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr17[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr18[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr19[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr20[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    //uint32_t mr23[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr24[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr25[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr28[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr37[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr40[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint32_t mr41[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    //uint32_t mr46[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR1
    uint8_t write_latency[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            ck_mode[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR2
    uint8_t nwr[cinit_cfg->num_pstates][cinit_cfg->num_dch], rl_nrtp[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR3
    uint8_t pdds[cinit_cfg->num_pstates][cinit_cfg->num_dch], bk_bg_org[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            wls[cinit_cfg->num_pstates][cinit_cfg->num_dch], read_dbi[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            write_dbi[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR10
    uint8_t rdqs_pst_mode[cinit_cfg->num_pstates][cinit_cfg->num_dch],rdqs_pre_2[cinit_cfg->num_pstates][cinit_cfg->num_dch],wck_pst[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            rdqs_pst[cinit_cfg->num_pstates][cinit_cfg->num_dch],rdqs_pre[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR11
    uint8_t dq_odt[cinit_cfg->num_pstates][cinit_cfg->num_dch], ca_odt[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            cs_odt_op[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR12
    uint8_t vref_ca[cinit_cfg->num_pstates][cinit_cfg->num_dch], vbs[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR13
    uint8_t thermal_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch], vro[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            dmd[cinit_cfg->num_pstates][cinit_cfg->num_dch], dual_vdd2[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR14
    uint8_t vref_dq_lwr[cinit_cfg->num_pstates][cinit_cfg->num_dch], vdlc[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR15
    uint8_t vref_dq_upr[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR16
    uint8_t fsp_wr[cinit_cfg->num_pstates][cinit_cfg->num_dch], fsp_op[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            cbt[cinit_cfg->num_pstates][cinit_cfg->num_dch], vrcg[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR17
    uint8_t soc_odt[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtd_ck[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            odtd_cs[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtd_ca[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            odtd[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR18
    uint8_t wck_odt[cinit_cfg->num_pstates][cinit_cfg->num_dch], wck_fm[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            wck_on[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            wck2ck_leveling[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            ckr[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR19
    uint8_t dvfsc[cinit_cfg->num_pstates][cinit_cfg->num_dch], dvfsq[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR20
    uint8_t rdqs[cinit_cfg->num_pstates][cinit_cfg->num_dch], wck_mode[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR22
    uint8_t rd_linkecc[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            wr_linkecc[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR23
    //uint8_t pasr_mask[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR24
    uint8_t dfeql[cinit_cfg->num_pstates][cinit_cfg->num_dch], dfequ[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            dfes[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR25
    uint8_t ck_bus_term[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            ca_bus_term[cinit_cfg->num_pstates][cinit_cfg->num_dch], parc[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR28
    uint8_t zq_reset[cinit_cfg->num_pstates][cinit_cfg->num_dch], zq_stop[cinit_cfg->num_pstates][cinit_cfg->num_dch],
            zq_int[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR37
    uint8_t wck2dqi_runtime[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR40
    uint8_t wck2dqo_runtime[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR41
    uint8_t pdfec[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint8_t nt_dq_odt[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint8_t edvfsc_odt_support[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    uint8_t dvfsc_edvfsc_support[cinit_cfg->num_pstates][cinit_cfg->num_dch];
    // MR46
    //uint8_t enh_rdqs[cinit_cfg->num_pstates][cinit_cfg->num_dch];

    // To set field name for "physetup_set_user_input".
    // Note that the number of char needs to be expanded if the length of string is longer than 32.
    char temp_str[32];

    // Stores pstates no of frequency sets, as for dynamic frequency ratio change order of pstates is not fixed.
    uint32_t cfg_pstates_no[cinit_cfg->num_pstates];

    uint8_t DisableRetraining;

    hdlr = cinit_cfg;

    train_2d = 0;
    pllbypass = 0;

    if ((cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY)
            && (cinit_cfg->spdData_m.sdram_protocol == DWC_LPDDR4)) {
        if (cinit_cfg->spdData_m.use_lpddr4x == 0) {
            SNPS_ERROR("SDRAM protocol LPDDR4 (%u) not supported in LPDDR5X4 phy (%u)",
                    cinit_cfg->spdData_m.sdram_protocol, cinit_cfg->ddrPhyType_m);
            dwc_ddrctl_cinit_exit(1);
        }
    }

    // put the mode register settings into a format suitable for dwc_ddrphy_phyinit_setUserInput
    for (uint32_t ii = 0; ii < cinit_cfg->num_pstates; ii++) {
        for (uint32_t jj = 0; jj < cinit_cfg->num_dch; jj++) {
            if (IS_LPDDR4) {
                SNPS_LOG("dwc_cinit_phyinit_setuserinput: pstate = %d IS_LPDDR4 = %d", ii,
                        IS_LPDDR4);
                {
                    INITMR0_t *const ptr[2] = { &REGB_FREQ_CH0(ii).initmr0,
                                                &REGB_FREQ_CH0(ii).initmr0 };
                    mr1[ii][jj] = ptr[jj]->mr;
                    mr2[ii][jj] = ptr[jj]->emr;
                }
                {
                    INITMR1_t *const ptr[2] = { &REGB_FREQ_CH0(ii).initmr1,
                                                &REGB_FREQ_CH0(ii).initmr1 };
                    mr3[ii][jj] = ptr[jj]->emr2;
                    mr13[ii][jj] = ptr[jj]->emr3;
                }
                {
#ifdef MEMC_DDR4_OR_LPDDR4
                    INITMR2_t *const ptr[2] = { &REGB_FREQ_CH0(ii).initmr2,
                                                &REGB_FREQ_CH0(ii).initmr2 };
                    mr11[ii][jj] = ptr[jj]->mr4;
                    mr12[ii][jj] = ptr[jj]->mr5;
#endif
                }
                {
#ifdef MEMC_DDR4_OR_LPDDR4
                    INITMR3_t *const ptr[2] = { &REGB_FREQ_CH0(ii).initmr3,
                                                &REGB_FREQ_CH0(ii).initmr3 };
                    mr22[ii][jj] = ptr[jj]->mr22;
#endif
                }
            } else if (IS_LPDDR5) {
                SNPS_LOG("dwc_cinit_phyinit_setuserinput: pstate = %d IS_LPDDR5 = %d", ii,
                        IS_LPDDR5);
                lpddr5_mode_registers_t *mr = &(cinit_cfg->memCtrlr_m.lpddr5_mr[ii]);
                //MR1
                write_latency[ii][jj] = mr->mr1.write_latency;
                ck_mode[ii][jj] = mr->mr1.ck_mode;
                mr1[ii][jj] = ((ck_mode[ii][jj] & 0x1) << 3) | ((write_latency[ii][jj] & 0xf) << 4);
                //MR2
                nwr[ii][jj] = mr->mr2.nwr;
                rl_nrtp[ii][jj] = mr->mr2.rl_nrtp;
                mr2[ii][jj] = (rl_nrtp[ii][jj] & 0xf) | ((nwr[ii][jj] & 0xf) << 4);
                //MR3
                pdds[ii][jj] = mr->mr3.pdds;
                bk_bg_org[ii][jj] = mr->mr3.bk_bg_org;
                wls[ii][jj] = mr->mr3.wls;
                read_dbi[ii][jj] = mr->mr3.read_dbi;
                write_dbi[ii][jj] = mr->mr3.write_dbi;
                mr3[ii][jj] = (pdds[ii][jj] & 0x7) | ((bk_bg_org[ii][jj] & 0x3) << 3)
                        | ((wls[ii][jj] & 0x1) << 5) | ((read_dbi[ii][jj] & 0x1) << 6)
                        | ((write_dbi[ii][jj] & 0x1) << 7);
                //MR10
                wck_pst[ii][jj] = mr->mr10.wck_pst;
                rdqs_pre[ii][jj] = mr->mr10.rdqs_pre;
                rdqs_pst[ii][jj] = mr->mr10.rdqs_pst;
                mr10[ii][jj] = ((wck_pst[ii][jj] & 0x3) << 2) | ((rdqs_pre[ii][jj] & 0x3) << 4)
                        | ((rdqs_pst[ii][jj] & 0x3) << 6);
                //MR11
                dq_odt[ii][jj] = mr->mr11.dq_odt;
                ca_odt[ii][jj] = mr->mr11.ca_odt;
                cs_odt_op[ii][jj] = mr->mr11.cs_odt_op;
                mr11[ii][jj] = (dq_odt[ii][jj] & 0x7) | ((ca_odt[ii][jj] & 0x7) << 4)
                        | ((cs_odt_op[ii][jj] & 0x1) << 7);
                //MR12
                vref_ca[ii][jj] = mr->mr12.vref_ca;
                vbs[ii][jj] = mr->mr12.vbs;
                mr12[ii][jj] = (vref_ca[ii][jj] & 0x7f) | ((vbs[ii][jj] & 0x1) << 7);
                //MR13
                thermal_offset[ii][jj] = mr->mr13.thermal_offset;
                vro[ii][jj] = mr->mr13.vro;
                dmd[ii][jj] = mr->mr13.dmd;
                dual_vdd2[ii][jj] = mr->mr13.dual_vdd2;
                mr13[ii][jj] = (thermal_offset[ii][jj] & 0x3) | ((vro[ii][jj] & 0x1) << 2)
                        | ((dmd[ii][jj] & 0x1) << 5) | ((dual_vdd2[ii][jj] & 0x1) << 7);
                //MR14
                vref_dq_lwr[ii][jj] = mr->mr14.vref_dq;
                vdlc[ii][jj] = mr->mr14.vdlc;
                mr14[ii][jj] = (vref_dq_lwr[ii][jj] & 0x7f) | ((vdlc[ii][jj] & 0x1) << 7);
                //MR15
                vref_dq_upr[ii][jj] = mr->mr15.vref_dq;
                mr15[ii][jj] = (vref_dq_upr[ii][jj] & 0x7f);
                //MR16
                fsp_wr[ii][jj] = mr->mr16.fsp_wr;
                fsp_op[ii][jj] = mr->mr16.fsp_op;
                cbt[ii][jj] = mr->mr16.cbt;
                vrcg[ii][jj] = mr->mr16.vrcg;
                mr16[ii][jj] = (fsp_wr[ii][jj] & 0x3) | ((fsp_op[ii][jj] & 0x3) << 2)
                        | ((cbt[ii][jj] & 0x3) << 4) | ((vrcg[ii][jj] & 0x1) << 6);
                //MR17
                soc_odt[ii][jj] = mr->mr17.soc_odt;
                odtd_ck[ii][jj] = mr->mr17.odtd_ck;
                odtd_cs[ii][jj] = mr->mr17.odtd_cs;
                odtd_ca[ii][jj] = mr->mr17.odtd_ca;
                odtd[ii][jj] = mr->mr17.odtd;
                mr17[ii][jj] = (soc_odt[ii][jj] & 0x7) | ((odtd_ck[ii][jj] & 0x1) << 3)
                        | ((odtd_cs[ii][jj] & 0x1) << 4) | ((odtd_ca[ii][jj] & 0x1) << 5)
                        | ((odtd[ii][jj] & 0x3) << 6);
                //MR18
                wck_odt[ii][jj] = mr->mr18.wck_odt;
                wck_fm[ii][jj] = mr->mr18.wck_fm;
                wck_on[ii][jj] = mr->mr18.wck_on;
                wck2ck_leveling[ii][jj] = mr->mr18.wck2ck_leveling;
                ckr[ii][jj] = mr->mr18.ckr;
                mr18[ii][jj] = (wck_odt[ii][jj] & 0x7) | ((wck_fm[ii][jj] & 0x1) << 3)
                        | ((wck_on[ii][jj] & 0x1) << 4) | ((wck2ck_leveling[ii][jj] & 0x1) << 6)
                        | ((ckr[ii][jj] & 0x1) << 7);
                //MR19
                dvfsc[ii][jj] = mr->mr19.dvfsc;
                dvfsq[ii][jj] = mr->mr19.dvfsq;
                mr19[ii][jj] = (dvfsc[ii][jj] & 0x3) | ((dvfsq[ii][jj] & 0x3) << 2);
                //MR20
                rdqs[ii][jj] = mr->mr20.rdqs;
                wck_mode[ii][jj] = mr->mr20.wck_mode;
                mr20[ii][jj] = (rdqs[ii][jj] & 0x3) | ((wck_mode[ii][jj] & 0x3) << 2);
                //MR22
                rd_linkecc[ii][jj] = mr->mr22.recc;
                wr_linkecc[ii][jj] = mr->mr22.wecc;
                mr22[ii][jj] = ((wr_linkecc[ii][jj] & 0x3) << 4)
                        | ((rd_linkecc[ii][jj] & 0x3) << 6);
                //MR23
                //pasr_mask[ii][jj]= mr->mr23.pasr_mask;
                //mr23[ii][jj] = (pasr_mask[ii][jj]&0xff);
                //MR24
                dfeql[ii][jj] = mr->mr24.dfeql;
                dfequ[ii][jj] = mr->mr24.dfequ;
                dfes[ii][jj] = ((mr->mr24.dfequ > 0) || (mr->mr24.dfeql > 0)) ? 0x1 : 0x0;
                mr24[ii][jj] = (dfeql[ii][jj] & 0x7) | ((dfequ[ii][jj] & 0x7) << 4)
                        | ((dfes[ii][jj] & 0x1) << 7);
                //MR25
                ck_bus_term[ii][jj] = mr->mr25.ck_bus_term;
                ca_bus_term[ii][jj] = mr->mr25.ca_bus_term;
                parc[ii][jj] = mr->mr25.parc;
                mr25[ii][jj] = ((ck_bus_term[ii][jj] & 0x1) << 4)
                        | ((ca_bus_term[ii][jj] & 0x1) << 5) | ((parc[ii][jj] & 0x1) << 6);
                //MR28
                zq_reset[ii][jj] = mr->mr28.zq_reset;
                zq_stop[ii][jj] = mr->mr28.zq_stop;
                zq_int[ii][jj] = mr->mr28.zq_int;
                mr28[ii][jj] = (zq_reset[ii][jj] & 0x1) | ((zq_stop[ii][jj] & 0x1) << 1)
                        | ((zq_int[ii][jj] & 0x3) << 2);
                //MR37
                wck2dqi_runtime[ii][jj] = mr->mr37.wck2dqi_runtime;
                mr37[ii][jj] = (wck2dqi_runtime[ii][jj] & 0xff);
                //MR40
                wck2dqo_runtime[ii][jj] = mr->mr40.wck2dqo_runtime;
                mr40[ii][jj] = (wck2dqo_runtime[ii][jj] & 0xff);
                //MR41
                pdfec[ii][jj] = mr->mr41.pdfec;
                nt_dq_odt[ii][jj] = mr->mr41.nt_dq_odt;
                edvfsc_odt_support[ii][jj] = mr->mr41.edvfsc_odt_support;
                dvfsc_edvfsc_support[ii][jj] = mr->mr41.dvfsc_edvfsc_support;
                mr41[ii][jj] =
                      ((nt_dq_odt[ii][jj] & 0x3) << 5)
                    | ((edvfsc_odt_support[ii][jj] & 0x1) << 3)
                    | ((dvfsc_edvfsc_support[ii][jj] & 0x2) << 1)
                    | ((pdfec[ii][jj] & 0x1))
                ;
                //MR46
                //enh_rdqs[ii][jj]= mr->mr46.enh_rdqs;
                //mr46[ii][jj] = (enh_rdqs[ii][jj]&0x1);
            } else {
                SNPS_ERROR("sdram_protocol = %u not yet supported", SPD.sdram_protocol);
            }

        } // jj -> dch
    } // ii -> pstates

    if (IS_LPDDR4) {
        dram_type = DWC_LPDDR4;
    } else if (IS_LPDDR5) {
        dram_type = DWC_LPDDR5;
    } else {
        SNPS_ERROR("sdram_protocol = %u not yet supported", SPD.sdram_protocol);
    }
    if (IS_UDIMM) {
        dimm_type = 0;
    }
    if (IS_NODIMM) {
        dimm_type = 4;
    }
    // When MEMC_SIDEBAND_ECC was defined, it indicates the ECC was enabled.
    // ECC byte always use the most significant byte, so both of num_dbyte and enabled_dq should been considered as FBW
    // For HBW/QBW, disabled_dbyte should be used to skip the un-connected dbytes.
    // But, for SNPS_DIMM, an extra define VIRL_DIMM_ECC_MODE_0 will be used to indicate the ECC device won't be used.
    // So, when VIRL_DIMM_ECC_MODE_0 is defined, the num_dbyte shouldn't take into account ECC width.
#ifdef MEMC_SIDEBAND_ECC
    if ((SPD.module_type == DWC_LRDIMM) && (REGB_DDRC_CH0.ecccfg0.ecc_mode == 0)) {
        num_dbyte = MEMC_DRAM_DATA_WIDTH / 8;
    } else {
        num_dbyte = MEMC_DRAM_TOTAL_DATA_WIDTH / 8;
    }
#else
  if( cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL ) {
#ifdef LPDDR_2MC1PHY
      num_dbyte = 2*MEMC_DRAM_DATA_WIDTH/8;
#else
      num_dbyte = MEMC_DRAM_DATA_WIDTH/8;
  } else if (cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
      num_dbyte = MEMC_DRAM_DATA_WIDTH/8/2;
  } else  { // QUARTER_BUS_WIDTH
      num_dbyte = MEMC_DRAM_DATA_WIDTH/8/4;
#endif
  }
#endif
#ifdef UMCTL2_QUAD_DFI
  if( cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL ) {
    num_dbyte = num_dbyte /2;
  }
#endif // UMCTL2_QUAD_DFI
    //#############################################################################
    //
    // Structure for basic (mandatory) user inputs
    //
    //#############################################################################

#ifdef MEMC_LPDDR4
    uint8_t LPDDR4X_Enable = (SPD.use_lpddr4x == 1) ? 1 : 0;
    if (IS_LPDDR4) {
        physetup_set_user_input(cinit_cfg, "Lp4xMode", LPDDR4X_Enable);
        if (LPDDR4X_Enable == 1) {
          if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
            physetup_set_user_input(cinit_cfg, "HardMacroVer", 0); // phyinit constraint
          }
          if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
#ifdef DWC_PHYINIT_RID_GE202311
            //LPDDR54 PHY PHYINIT 2023.11 has removed unused "HardMacroVer"
#else
            physetup_set_user_input(cinit_cfg, "HardMacroVer", 0); // phyinit constraint
#endif  //DWC_PHYINIT_RID_GE202311 
          }
        }
    }
#endif //MEMC_LPDDR4
#ifdef MEMC_LPDDR5X
    uint8_t LPDDR5X_Enable = (SPD.use_lpddr5x == 1) ? 1 : 0;
    if (IS_LPDDR5) {
        physetup_set_user_input(cinit_cfg, "Lp5xMode", LPDDR5X_Enable);
    }
#endif //MEMC_LPDDR5X
    physetup_set_user_input(cinit_cfg, "DramType", dram_type);
    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
        physetup_set_user_input (cinit_cfg, "DMEMLoadPerfEn", 0);
    }

    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
#ifdef DDRCTL_HWFFC_EXT
        //1:2 mode & num freq > 2
        if((cinit_cfg->num_pstates > 4) && 
            ((DWC_RATIO_1_2 == ddrctl_sw_get_ratio(cinit_cfg, 0)) ||
             (DWC_RATIO_WCK_CK_2_1 == ddrctl_sw_get_ratio(cinit_cfg, 0)))) {
            cinit_cfg->num_pstates = 7;
        }
#endif //DDRCTL_HWFFC_EXT
    }
    physetup_set_user_input(cinit_cfg, "NumPStates", cinit_cfg->num_pstates);
  
#ifdef DWC_DDRPHY_MMFW_EN
    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
      physetup_set_user_input(cinit_cfg, "DramStateChangeEn",0);
    }
  #if defined (DDRCTL_HWFFC_EXT) && defined (MEMC_LPDDR5X)
    // set mmfwEn=1 for controller verification tests with P14
    physetup_set_user_input(cinit_cfg, "mmfwEn",1);
  #else
    // For 14 PState, if mmfwEn==0, only allow a max of 4 Pstate's, if >4 Pstate's is required then MMFW must be loaded
    if ((cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) && (cinit_cfg->num_pstates > 4)) {
      physetup_set_user_input(cinit_cfg, "mmfwEn",1);
    }
  #endif
#endif

#ifdef DWC_PHYINIT_RID_GE202308
    if (cinit_cfg->ddrPhyType_m = DWC_LPDDR5X4_PHY) {
      if (IS_LPDDR5) {
        physetup_set_user_input(cinit_cfg, "UseSnpsController",1);
      }
    }
#endif

    cfg_pstates = 0x0000;
    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
        for (int pstates = 0; pstates < cinit_cfg->num_pstates; pstates++) {
            cfg_pstates = cfg_pstates | (0x1 << (pstates));
        }
    } else {
        for(int pstates=0;pstates<cinit_cfg->num_pstates;pstates++) {
            if ((cinit_cfg->num_pstates <= 2) || 
                ((cinit_cfg->num_pstates <= 4) &&
                 ((DWC_RATIO_1_4 == ddrctl_sw_get_ratio(cinit_cfg, pstates)) ||
                  (DWC_RATIO_WCK_CK_4_1 == ddrctl_sw_get_ratio(cinit_cfg, pstates)))) ||
                ((cinit_cfg->num_pstates > 4) &&
                 ((DWC_RATIO_1_4 == ddrctl_sw_get_ratio(cinit_cfg, 0)) ||
                  (DWC_RATIO_WCK_CK_4_1 == ddrctl_sw_get_ratio(cinit_cfg, 0))))) {
                cfg_pstates = cfg_pstates | (0x1 << (pstates));
            } else {
                cfg_pstates = cfg_pstates | (0x1 << (0x7+pstates));
            }
        } 
    }

    SNPS_INFO("Config pStates 0x%x", cfg_pstates);

    // Check first pState
    if (((DWC_RATIO_1_2 == ddrctl_sw_get_ratio(cinit_cfg, 0)) || 
         (DWC_RATIO_WCK_CK_2_1 == ddrctl_sw_get_ratio(cinit_cfg, 0))) 
         && (cinit_cfg->num_pstates > 2)) { //1:2 mode & num freq > 2
        first_pstate = (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) ? 0x0000 : 0x0007;
    } else {
        first_pstate = 0x0000;
    }

    SNPS_INFO("First pState 0x%x", first_pstate);

    // This code is only to set the cfg_pstates_no[p] value. The value will only be used in prints
    // Verify if this can be removed
    uint32_t freq_ratio_0_cnt = 0x0;
    uint32_t freq_ratio_1_cnt = 0x0;

    freq_ratio_0_cnt = 0x0;
    freq_ratio_1_cnt = 0x0;
    for (int p = 0; p < cinit_cfg->num_pstates; p++) {

      for(int i=0 ; i < DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;i++) {
        if (cinit_cfg->ddrPhyType_m != DWC_LPDDR5X4_PHY) {
           if((DWC_RATIO_1_4 == ddrctl_sw_get_ratio(cinit_cfg, p)) ||
              (DWC_RATIO_WCK_CK_4_1 == ddrctl_sw_get_ratio(cinit_cfg, p)) ||
               cinit_cfg->num_pstates < 3) {
             if (((cfg_pstates) & (0x1 << (freq_ratio_1_cnt+i))) == 0) {
               continue;
             }
               cfg_pstates_no[p] = freq_ratio_1_cnt+i;
               freq_ratio_1_cnt = freq_ratio_1_cnt+i+1;
               break;
           } else {
             if (((cfg_pstates) & (0x1 << (0x7+freq_ratio_0_cnt+i))) == 0) {
               continue;
             }
               cfg_pstates_no[p] = 0x7+freq_ratio_0_cnt+i;
               freq_ratio_0_cnt = freq_ratio_0_cnt+i+1;
               break;
           }
        } else if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
             if (((cfg_pstates) & (0x1 << (freq_ratio_1_cnt+i))) == 0) {
               continue;
             }
               cfg_pstates_no[p] = freq_ratio_1_cnt+i;
               freq_ratio_1_cnt = freq_ratio_1_cnt+i+1;
               break;
        }
     }
    }

    physetup_set_user_input(cinit_cfg, "CfgPStates", cfg_pstates);            //TODO Bug_7504, Comment_17
    physetup_set_user_input(cinit_cfg, "FirstPState", first_pstate);
    if(SPD.num_ranks==4){
      //Incorrect programming for NumRank_dfi0 with illegal value of 4, as Legal values are: 1, 2
      physetup_set_user_input(cinit_cfg, "NumRank_dfi0", SPD.num_ranks/2);
    } else {
      physetup_set_user_input(cinit_cfg, "NumRank_dfi0", SPD.num_ranks);
    }
    uint8_t DisablePhyUpdate = (REGB_DDRC_CH0.dfiupd0.dfi_phyupd_en == 1) ? 0 : 1;
#ifdef DWC_DDRPHY_MMFW_EN
    // For 14 PState, only support DisablePhyUpdate==1
    physetup_set_user_input(cinit_cfg, "DisablePhyUpdate", 1);
#else
    physetup_set_user_input(cinit_cfg, "DisablePhyUpdate", DisablePhyUpdate);
#endif
    physetup_set_user_input(cinit_cfg, "DisablePmuEcc", 1);

    if (IS_LPDDR5) {
        uint8_t DqsOscRunTimeSel =
#ifdef DWC_PHYINIT_RID_GE202212
      // LPDDR5X4 phyinit constraint
      // DqsOscRunTimeSel = 0x3 (DRAM OSC Runtime = 2048tCK) is used during retraining by phyinit.
                    3;
#else
                (REGB_DDRC_CH0.dqsoscruntime.dqsosc_runtime == 0) ? 3 : // MC doesn't support dqsosc_runtime==0 - set default
                (REGB_DDRC_CH0.dqsoscruntime.dqsosc_runtime < 0x40) ?
                    REGB_DDRC_CH0.dqsoscruntime.dqsosc_runtime * 16 / 256 - 1 : // 0x01 to 0x3F - < 1024 memCK
                (REGB_DDRC_CH0.dqsoscruntime.dqsosc_runtime < 0x80) ? 3 : // 0x40 to 0x7F - 2048 memCK
                (REGB_DDRC_CH0.dqsoscruntime.dqsosc_runtime < 0xC0) ? 4 : // 0x80 to 0xBF - 4096 memCK
                    5;     // 0xC0 to 0xFF - 8192 memCK
#endif
        physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[0]", DqsOscRunTimeSel);
        physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[1]", DqsOscRunTimeSel);
        physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[2]", DqsOscRunTimeSel);
        physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[3]", DqsOscRunTimeSel);
        if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[4]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[5]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[6]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[7]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[8]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[9]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[10]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[11]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[12]", DqsOscRunTimeSel);
            physetup_set_user_input(cinit_cfg, "DqsOscRunTimeSel[13]", DqsOscRunTimeSel);
        }
    }

    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
        //  1024 entries per Pstate. RAM is 16k deep when all PStates are in use
        physetup_set_user_input(cinit_cfg, "PsDmaRamSize", 2);
    }
#ifdef DWC_DDRPHY_DFI1_EXISTS
    physetup_set_user_input(cinit_cfg, "Dfi1Exists", 1);
    if (IS_LPDDR4 && (cinit_cfg->lpddr4_pop_support == 1)) {
        if (cinit_cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_FULL) {
            dfi_mode = 3;
        } else {
            dfi_mode = 1;
        }
    } else {
        dfi_mode = 3;
    }
    if (cinit_cfg->lpddr4_pop_support == 1) {
        SNPS_LOG("lpddr4_pop_support = %d", cinit_cfg->lpddr4_pop_support);
    }
    if (IS_LPDDR4 && (cinit_cfg->lpddr4_pop_support == 1)) {
        SNPS_LOG("IS_LPDDR4 && pop", NULL);
    }
    if (dfi_mode == 1 && (dram_type == DWC_LPDDR4 || dram_type == DWC_LPDDR5)) { //dfi_mode=3( DFI0,DFI1) dram_type =2 (LPDDR4)
        num_active_dbyte_dfi0 = num_dbyte;
        num_active_dbyte_dfi1 = 0;
        physetup_set_user_input(cinit_cfg, "NumRank_dfi1", 0); // phyinit constraint P80001562-272842
    } else {
        num_active_dbyte_dfi0 = num_dbyte / 2;
        num_active_dbyte_dfi1 = num_dbyte - num_dbyte / 2;
        if(SPD.num_ranks==4){
          //Incorrect programming for NumRank_dfi1 with illegal value of 4, as Legal values are: 1, 2
          physetup_set_user_input(cinit_cfg, "NumRank_dfi1", SPD.num_ranks/2);
        } else {
          physetup_set_user_input(cinit_cfg, "NumRank_dfi1", SPD.num_ranks);
        }
    }
#else    //MEMC_DRAM_DATA_WIDTH=16,DFI0 only
#ifdef DWC_DDRPHY_NUM_CHANNELS_2
    #ifdef UMCTL2_QUAD_DFI
    if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL || cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
      dfi_mode=3;
    }
    #else 
    if(IS_LPDDR4 && (cinit_cfg->lpddr4_pop_support==1)) {
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL) {
            dfi_mode=3;
        } else {
            dfi_mode=1;
        }
    } else if(IS_LPDDR5 ) {
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL) {
            dfi_mode=3;
        } else {
            dfi_mode=1;
        }
    } else {
        dfi_mode=3;
    }
    #endif // UMCTL2_QUAD_DFI
    if(cinit_cfg->lpddr4_pop_support == 1) {
        SNPS_LOG("lpddr4_pop_support = %d", cinit_cfg->lpddr4_pop_support);
    }
    if(IS_LPDDR4) {
        SNPS_LOG("IS_LPDDR4,dfi_mode = %d", dfi_mode);
    }
    if(IS_LPDDR5) {
        SNPS_LOG("IS_LPDDR5,dfi_mode = %d", dfi_mode);
    }
    if(IS_LPDDR4 && (cinit_cfg->lpddr4_pop_support == 1)) {
        SNPS_LOG("IS_LPDDR4 && pop", NULL);
    }
    if(dfi_mode==1 && (dram_type == DWC_LPDDR4 || dram_type == DWC_LPDDR5) ) {  //dfi_mode=3( DFI0,DFI1) dram_type =2 (LPDDR4)
        num_active_dbyte_dfi0= num_dbyte;
        num_active_dbyte_dfi1=0;
        physetup_set_user_input(cinit_cfg, "NumRank_dfi1", 0); // phyinit constraint P80001562-272842
    } else {
        num_active_dbyte_dfi0= num_dbyte/2;
        num_active_dbyte_dfi1=num_dbyte-num_dbyte/2;
        if(SPD.num_ranks==4){
          //Incorrect programming for NumRank_dfi1 with illegal value of 4, as Legal values are: 1, 2
        physetup_set_user_input(cinit_cfg, "NumRank_dfi1", SPD.num_ranks/2);
        } else {
        physetup_set_user_input(cinit_cfg, "NumRank_dfi1", SPD.num_ranks);
        }
    }
#else
#ifdef DWC_LPDDR5XPHY_NUM_CHANNELS_2
    #ifdef UMCTL2_QUAD_DFI
    if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL || cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
      dfi_mode=3;
    }
    #else
    if(IS_LPDDR4 && (cinit_cfg->lpddr4_pop_support==1)) {
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL) {
            dfi_mode=3;
        } else {
            dfi_mode=1;
        }
    } else if(IS_LPDDR5 ) {
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL) {
            dfi_mode=3;
        } else {
            dfi_mode=1;
        }
    } else {
        dfi_mode=3;
    }
    #endif // UMCTL2_QUAD_DFI
    if(cinit_cfg->lpddr4_pop_support == 1) {
        SNPS_LOG("lpddr4_pop_support = %d", cinit_cfg->lpddr4_pop_support);
    }
    if(IS_LPDDR4) {
        SNPS_LOG("IS_LPDDR4,dfi_mode = %d", dfi_mode);
    }
    if(IS_LPDDR5) {
        SNPS_LOG("IS_LPDDR5,dfi_mode = %d", dfi_mode);
    }
    if(IS_LPDDR4 && (cinit_cfg->lpddr4_pop_support == 1)) {
        SNPS_LOG("IS_LPDDR4 && pop", NULL);
    }
    if(dfi_mode==1 && (dram_type == DWC_LPDDR4 || dram_type == DWC_LPDDR5) ) {  //dfi_mode=3( DFI0,DFI1) dram_type =2 (LPDDR4)
        num_active_dbyte_dfi0= num_dbyte;
        num_active_dbyte_dfi1=0;
        physetup_set_user_input(cinit_cfg, "NumRank_dfi1", 0); // phyinit constraint P80001562-272842
    } else {
        num_active_dbyte_dfi0= num_dbyte/2;
        num_active_dbyte_dfi1=num_dbyte-num_dbyte/2;
        if(SPD.num_ranks==4){
          //Incorrect programming for NumRank_dfi1 with illegal value of 4, as Legal values are: 1, 2
          physetup_set_user_input(cinit_cfg, "NumRank_dfi1", SPD.num_ranks/2);
        } else {
          physetup_set_user_input(cinit_cfg, "NumRank_dfi1", SPD.num_ranks);
        }
    }
#else
    num_active_dbyte_dfi0= num_dbyte;
    num_active_dbyte_dfi1=0;
    physetup_set_user_input (cinit_cfg, "NumRank_dfi1",0);
    dfi_mode=1; //DFI0 enable only
#endif
#endif
#endif

    physetup_set_user_input(cinit_cfg, "NumActiveDbyteDfi0", num_active_dbyte_dfi0);
    physetup_set_user_input(cinit_cfg, "NumActiveDbyteDfi1", num_active_dbyte_dfi1);

    physetup_set_user_input(cinit_cfg, "DimmType", dimm_type);

    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
#ifdef DWC_DDRPHY_NUM_CHANNELS_1
        num_ch = 1;
#else
        num_ch = 2;
#endif
#ifdef DWC_DDRPHY_NUM_RANKS_1
        num_rank = 1;
#else
        num_rank = 2;
#endif
    } else {
#ifdef DWC_LPDDR5XPHY_NUM_CHANNELS_1
        num_ch = 1;
#else
        num_ch = 2;
#endif
#ifdef DWC_LPDDR5XPHY_NUM_RANKS_1
        num_rank = 1;
#else
        num_rank = 2;
#endif
    }

    //P80001562-170395 : num_dbytes_per_ch = 2 fixed for lpddr54. This code will be clean up in P80001562-182651
    //  #ifdef DWC_DDRPHY_NUM_DBYTES_PER_CHANNEL_2
    num_dbytes_per_ch = 2;
    //  #else
    //     num_dbytes_per_ch = 4;
    //  #endif

    physetup_set_user_input(cinit_cfg, "NumCh", num_ch);
    physetup_set_user_input(cinit_cfg, "NumRank", num_rank);
    physetup_set_user_input(cinit_cfg, "NumDbytesPerCh", num_dbytes_per_ch);
    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
#ifndef DWC_PHYINIT_RID_GE201908
        uint32_t dmi_dbi_en;
#ifdef DWC_DDRPHY_DBYTE_DMI_ENABLED
        dmi_dbi_en = 1;
#else
        dmi_dbi_en = 0;
#endif

        physetup_set_user_input(cinit_cfg, "DmiDbiEn", dmi_dbi_en);
#endif
    }

    // check that DramDataWidth is setup correctly
    if (IS_LPDDR4) {
        CONSTRAIN_NE(SPD.sdram_width_bits[0], 4);
        /*CONSTRAIN_NE(SPD.sdram_width_bits,32);*/
    }
    // MixedMode
    if ((SPD.sdram_width_bits[0]==16) && (SPD.sdram_width_bits[1]==8) && (SPD.num_ranks==2)) {
        physetup_set_user_input(cinit_cfg, "DramDataWidth", SPD.sdram_width_bits[1]);
    } else {
        physetup_set_user_input(cinit_cfg, "DramDataWidth", SPD.sdram_width_bits[0]);
    }
#ifdef DDRCTL_LPDDR

#ifdef DWC_DDRPHY_MMFW_EN
    // For 14 PState, only support DisableFspOp==1
    physetup_set_user_input(cinit_cfg, "DisableFspOp", 1);
#else
    physetup_set_user_input(cinit_cfg, "DisableFspOp", cinit_cfg->disable_fsp_op);
#endif


    if(cinit_cfg->phy_training==DWC_PHY_SKIP_TRAINING) {
      if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
          //P80001562-408976 : enable Lp3DramState for LPDDR5X/5/4X PHY
          if (IS_LPDDR5) {
#ifdef DWC_PHYINIT_RID_GE202307
            physetup_set_user_input(cinit_cfg, "Lp3DramState[0]", cinit_cfg->enable_deep_sleep_mode);
            physetup_set_user_input(cinit_cfg, "Lp3DramState[1]", cinit_cfg->enable_deep_sleep_mode);
            physetup_set_user_input(cinit_cfg, "Lp3DramState[2]", cinit_cfg->enable_deep_sleep_mode);
            physetup_set_user_input(cinit_cfg, "Lp3DramState[3]", cinit_cfg->enable_deep_sleep_mode);
            if (cinit_cfg->num_pstates > 4) {
              physetup_set_user_input(cinit_cfg, "Lp3DramState[4]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[5]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[6]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[7]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[8]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[9]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[10]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[11]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[12]", cinit_cfg->enable_deep_sleep_mode);
              physetup_set_user_input(cinit_cfg, "Lp3DramState[13]", cinit_cfg->enable_deep_sleep_mode);
            }
#endif
          }
      }
        // Enable RetEn both for LPDDR5/LPDDR4 with LPDDR5/4X/4 PHY
        physetup_set_user_input(cinit_cfg, "RetEn", 1);

    // disable RetEn for devinit/training
    } else {
      physetup_set_user_input(cinit_cfg, "RetEn", 0);
    }

#ifdef DDRCTL_PPT2
    for(int p=0;p<cinit_cfg->num_pstates;p++) {
        sprintf(temp_str, "RetrainMode[%d]", cfg_pstates_no[p]);

        uint8_t pure_ppt2_enabled   = REGB_FREQ_CH0(p).dfiupdtmg2.ppt2_en && !REGB_FREQ_CH0(p).dfiupdtmg2.ppt2_override;
        uint8_t PPT2RetrainMode     = pure_ppt2_enabled ? 4 : 1;
        physetup_set_user_input(cinit_cfg, temp_str, PPT2RetrainMode);

        SNPS_LOG("PPT2RetrainMode: %s=%d", temp_str, PPT2RetrainMode);

#ifndef DWC_DDRPHY_MMFW_EN
        if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY && p>=4) { SNPS_ERROR("Attempt to set >4 PState"); } // setting PState>=4 is prohibited without MMFW
#endif

        if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY && pure_ppt2_enabled) { SNPS_ERROR("Attempt to enable PPT2 in LP5X PHY which is not supported. PState=%d", cfg_pstates_no[p]); }
    }
#endif // DDRCTL_PPT2

#endif // DDRCTL_LPDDR
    uint8_t freq_ratio[cinit_cfg->num_pstates];

    for(int p=0;p<cinit_cfg->num_pstates;p++) {
        // 1:1:4 Mode
        if ((DWC_RATIO_WCK_CK_4_1 == ddrctl_sw_get_ratio(cinit_cfg, p)) ||
            (DWC_RATIO_1_4 == ddrctl_sw_get_ratio(cinit_cfg, p))) { 
            freq_ratio[p] = 2;
        } else {
            freq_ratio[p] = 1;
        }
    }

    // Retraining is enabled only for phy training case.
    if(cinit_cfg->phy_training==DWC_PHY_SKIP_TRAINING) {
        DisableRetraining = 1;
    }
    else if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {
        DisableRetraining = 0;
    }
    else if(cinit_cfg->phy_training==DWC_PHY_DEV_INIT) {
        DisableRetraining = 1;
    }
    physetup_set_user_input(cinit_cfg, "DisableRetraining",DisableRetraining);

    for(int p=0;p<cinit_cfg->num_pstates;p++) {
        sprintf(temp_str, "DfiFreqRatio[%d]", cfg_pstates_no[p]);
        physetup_set_user_input(cinit_cfg, temp_str, freq_ratio[p]);

        uint32_t tck_ps=SPD.tck_ps[p];
        uint32_t freq=CEIL(1000000,tck_ps);
        // freq=CEIL(1000000,938) = 1067Mbps violates phyinit checker.
        // Set freq = 1066Mbps to avoid phyinit checker issue.
        if(IS_LPDDR5) {
            if (tck_ps == 938) {
              freq = 1066;
            }
        }
        if(IS_LPDDR5) {
          // deal with boundary frequncy for speed bin 7500Mbps
          // speed bin 7500Mbps: 6400 < data rate <= 7500Mbps, 800 < ck frequency <= 937.5Mbps
          // set userinput Frequency=937Mbps to make it in speed bin 7500Mbps when 937 < ck frequency <=937.5Mbps
          if (((1000000.0/tck_ps)<=937.5) && ((1000000.0/tck_ps)>937)) {
            freq=937;
          }
        }
        /*printf("Setting Frequency[%d]=%u\n",p, freq);*/
        // Memclk frequency in MHz round up to next highest integer
        sprintf(temp_str, "Frequency[%d]", cfg_pstates_no[p]);
        physetup_set_user_input(cinit_cfg, temp_str, freq);

        if(IS_LPDDR5) {
            if (ddrctl_sw_get_ratio(cinit_cfg, p) == DWC_RATIO_WCK_CK_4_1) {
                freqThreshold = 200;
                freqThreshold_pllbypass = 83;
            } else {
		freqThreshold = 400;
                freqThreshold_pllbypass = 166;
            }

            uint8_t RxClkTrackEn = (DisableRetraining == 1)? 0 : ((freq > freqThreshold) ? 1 : 0);
            pllbypass = (freq<freqThreshold_pllbypass) ? 1 : 0; // Note: PLL Bypass on/off settings must align with MC config. See 'm_b_bypass_clk_enable' in dwc_ddrctl_mss_cfg_essential_constraints.svh
            sprintf(temp_str, "RxClkTrackEn[%d]",cfg_pstates_no[p]);
            physetup_set_user_input(cinit_cfg, temp_str, RxClkTrackEn);
        }
        if(IS_LPDDR4) {
            freqThreshold_pllbypass = 333;
            freqThreshold = 800;
            pllbypass = (freq<freqThreshold_pllbypass) ? 1 : 0;
            uint8_t RxClkTrackEn = (DisableRetraining == 1)? 0 : ((freq>freqThreshold) ? 1 : 0);
            sprintf(temp_str, "RxClkTrackEn[%d]", cfg_pstates_no[p]);
            physetup_set_user_input(cinit_cfg, temp_str, RxClkTrackEn);
        }

        sprintf(temp_str, "PllBypass[%d]", cfg_pstates_no[p]);
        physetup_set_user_input(cinit_cfg, temp_str, pllbypass);
    }

    if(SPD.num_ranks==4) {
        cs_present_cha=0xf;
    } else if(SPD.num_ranks==2) {
        cs_present_cha=0x3;
    } else {
        cs_present_cha=0x1;
    }
    cs_present_chb = 0;

    if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL && dfi_mode==3) {
        cs_present_chb = cs_present_cha;
    }

//#############################################################################
//
// Structure for advanced (optional) user inputs
// - if user does not enter a value for these parameters, a PHY recommended or
//   default value will be used
//
//#############################################################################
#ifdef MEMC_LPDDR4
#ifdef DWC_PHYINIT_RID_GE202306
    //"WDQSExt" has been removed in PHYINIT version 2023.06
    //Removed PHYINIT UserInput "WDQSExt" and hardcode programming of WDQSEXTENSION feature
#else
    if(IS_LPDDR4) {
        if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
            physetup_set_user_input(cinit_cfg, "WDQSExt", 0); // TODO add some variable to control this
        }

    }
#endif //DWC_PHYINIT_RID_GE202306
#endif //MEMC_LPDDR4

    //#############################################################################
    //
    // Structure for user input simulation options
    //
    //#############################################################################
#ifdef MEMC_LPDDR4
    if(IS_LPDDR4) {
        ddrTimingParameters_t* timing = &(cinit_cfg->timingParams_m[0][0]);
        physetup_set_user_input(cinit_cfg, "tDQS2DQ",timing->lpddr4_tdqs2dq);
        physetup_set_user_input(cinit_cfg, "tDQSCK",timing->lpddr4_tdqsck);
    }
    if(IS_LPDDR5) {
        ddrTimingParameters_t* timing = &(cinit_cfg->timingParams_m[0][0]);
        // set tWCK2DQI & tWCK2DQO to SVT VIP values
        physetup_set_user_input(cinit_cfg, "tWCK2DQI",timing->lpddr5_wckdqi_ps);
        physetup_set_user_input(cinit_cfg, "tWCK2DQO",timing->lpddr5_wckdqo_ps);

         // Snoop enable
         for(int p=0;p<cinit_cfg->num_pstates;p++) {
           sprintf(temp_str, "EnWck2DqoTracking[%d]", cfg_pstates_no[p]);
           physetup_set_user_input(cinit_cfg, temp_str, cinit_cfg->EnWck2DqoTracking);
         }
    }
#endif //MEMC_LPDDR4

    //#############################################################################
    //
    // Structure for RuntimeConfig options
    //
    //#############################################################################
    if(cinit_cfg->phy_training==DWC_PHY_SKIP_TRAINING) {
        physetup_set_user_input(cinit_cfg, "initCtrl",0xf);
        physetup_set_user_input(cinit_cfg, "skip_train",1);
    }
    else if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {
        physetup_set_user_input(cinit_cfg, "initCtrl",0x0);
        physetup_set_user_input(cinit_cfg, "skip_train",0);
    }
    else if(cinit_cfg->phy_training==DWC_PHY_DEV_INIT) {
        physetup_set_user_input(cinit_cfg, "initCtrl",0x21);
        physetup_set_user_input(cinit_cfg, "skip_train",2);
    }

    if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
        #ifdef DWC_PHYINIT_RID_GE202210
        //#############################################################################
        //LPDDR54 PHYINIT C-2022.10
        //Removed unused User Input parameter "PhyMstrCtrlMode" and related PHYINIT code
        //#############################################################################
        #else
        //#############################################################################
        // When this bit is 0, a PHY Master transaction is initiated only by timer function.
        //#############################################################################
        if(cinit_cfg->PhyMstrCtrlMode==0) {
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[0]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[1]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[2]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[3]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[4]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[5]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[6]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[7]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[8]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[9]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[10]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[11]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[12]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[13]", cinit_cfg->PhyMstrCtrlMode);
            physetup_set_user_input(cinit_cfg, "PhyMstrCtrlMode[14]", cinit_cfg->PhyMstrCtrlMode);
        }
        #endif //DWC_PHYINIT_RID_GE202210
    }
    if(cinit_cfg->PhyMstrTrainInterval>0) {
        //#############################################################################
        // change phymstr interval
        //#############################################################################
        if (cinit_cfg->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
	  if(cinit_cfg->PhyMstrTrainInterval>0xb) {
          //PHYINIT checks that interval is not greater than 0xb although bigger values are supported in RTL
	  // Set both PhyMstrMaxReqToAck & PhyMstrTrainInterval to 1024
          cinit_cfg->PhyMstrTrainInterval = 0xb;
          }
	}
        physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[0]", cinit_cfg->PhyMstrTrainInterval);
        physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[1]", cinit_cfg->PhyMstrTrainInterval);
        physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[2]", cinit_cfg->PhyMstrTrainInterval);
        physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[3]", cinit_cfg->PhyMstrTrainInterval);
        if (cinit_cfg->ddrPhyType_m == DWC_LPDDR54_PHY) {
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[4]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[5]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[6]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[7]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[8]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[9]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[10]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[11]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[12]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[13]", cinit_cfg->PhyMstrTrainInterval);
            physetup_set_user_input(cinit_cfg, "PhyMstrTrainInterval[14]", cinit_cfg->PhyMstrTrainInterval);
        }
    }

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
    uint32_t msgmisc;
    msgmisc = 0;
    if(cinit_cfg->use_jedec_init==0) {msgmisc |= 1 << 1;}
    msgmisc |= 1 << 2;
    if(IS_DDR4 && !(IS_LRDIMM) ) {
        msgmisc |= 1 << 3;
    }
    #ifdef UMCTL2_SHARED_AC
    msgmisc |= 1 << 6;
    #endif
    enabled_dq_cha = num_active_dbyte_dfi0 * 8;
    enabled_dq_chb = num_active_dbyte_dfi1 * 8;
    for(int i=0;i<cinit_cfg->num_pstates;i++) {
        for(int j=0;j<1;j++) {  // Hardcode 1 as PHY supports only 1 channel
            physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MsgMisc", msgmisc, train_2d);
            physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "HdtCtrl",cinit_cfg->HdtCtrl , train_2d);// Stage completion
            physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "DFIMRLMargin", 1, train_2d);
            if(IS_LPDDR4) {
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "EnabledDQsChA", enabled_dq_cha, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "CsPresentChA", cs_present_cha, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_A0", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_A0", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_A0", (mr3[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_A0", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_A0", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_A0", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_A0", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_A0", (mr22[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_A1", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_A1", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_A1", (mr3[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_A1", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_A1", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_A1", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_A1", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_A1", (mr22[i][j] & 0xff), train_2d);

                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "EnabledDQsChB", enabled_dq_chb, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "CsPresentChB", cs_present_chb, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_B0", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_B0", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_B0", (mr3[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_B0", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_B0", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_B0", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_B0", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_B0", (mr22[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_B1", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_B1", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_B1", (mr3[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_B1", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_B1", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_B1", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_B1", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_B1", (mr22[i][j] & 0xff), train_2d);
            }
            else if(IS_LPDDR5) {
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "EnabledDQsChA", enabled_dq_cha, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "CsPresentChA", cs_present_cha, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_A0", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_A0", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_A0", (mr3[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR10_A0", (mr10[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_A0", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_A0", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_A0", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_A0", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR15_A0", (mr15[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR16_A0", (mr16[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR17_A0", (mr17[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR18_A0", (mr18[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR19_A0", (mr19[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR20_A0", (mr20[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_A0", (mr22[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR24_A0", (mr24[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, i, "MR23_A0", (mr23[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR25_A0", (mr25[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR28_A0", (mr28[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR37_A0", (mr37[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR40_A0", (mr40[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR41_A0", (mr41[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR46_A0", (mr46[i][j] & 0xff), train_2d); // Comment out because MR46_* is not found
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_A1", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_A1", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_A1", (mr3[i][j] & 0xff), train_2d);

                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR10_A1", (mr10[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_A1", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_A1", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_A1", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_A1", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR15_A1", (mr15[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR16_A1", (mr16[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR17_A1", (mr17[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR18_A1", (mr18[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR19_A1", (mr19[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR20_A1", (mr20[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_A1", (mr22[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR24_A1", (mr24[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, i, "MR23_A1", (mr23[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR25_A1", (mr25[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR28_A1", (mr28[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR37_A1", (mr37[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR40_A1", (mr40[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR41_A1", (mr41[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR46_A1", (mr46[i][j] & 0xff), train_2d); // Comment out because MR46_* is not found

                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "EnabledDQsChB", enabled_dq_chb, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "CsPresentChB", cs_present_chb, train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_B0", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_B0", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_B0", (mr3[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR10_B0", (mr10[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_B0", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_B0", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_B0", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_B0", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR15_B0", (mr15[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR16_B0", (mr16[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR17_B0", (mr17[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR18_B0", (mr18[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR19_B0", (mr19[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR20_B0", (mr20[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_B0", (mr22[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR24_B0", (mr24[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, i, "MR23_B0", (mr23[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR25_B0", (mr25[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR28_B0", (mr28[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR37_B0", (mr37[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR40_B0", (mr40[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR41_B0", (mr41[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR46_B0", (mr46[i][j] & 0xff), train_2d); // Comment out because MR46_* is not found
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR1_B1", (mr1[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR2_B1", (mr2[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR3_B1", (mr3[i][j] & 0xff), train_2d);

                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR10_B1", (mr10[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR11_B1", (mr11[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR12_B1", (mr12[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR13_B1", (mr13[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR14_B1", (mr14[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR15_B1", (mr15[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR16_B1", (mr16[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR17_B1", (mr17[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR18_B1", (mr18[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR19_B1", (mr19[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR20_B1", (mr20[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR22_B1", (mr22[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR24_B1", (mr24[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, i, "MR23_B1", (mr23[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR25_B1", (mr25[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR28_B1", (mr28[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR37_B1", (mr37[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR40_B1", (mr40[i][j] & 0xff), train_2d);
                physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR41_B1", (mr41[i][j] & 0xff), train_2d);
                //physetup_set_msg_block (cinit_cfg, cfg_pstates_no[i], "MR46_B1", (mr46[i][j] & 0xff), train_2d); // Comment out because MR46_* is not found
            }
            //LPDDR3 and LPDDR4 1D
            // SequenceCtrl[0]    = 1     Run DevInit - Device/phy initialization. Should always be set.
            // SequenceCtrl[1]    = 1     Run WrLvl - Write leveling
            // SequenceCtrl[2]    = 1     Run RxEn - Read gate training
            // SequenceCtrl[3]    = 1     Run RdDQS1D - 1d read dqs training
            //
            // SequenceCtrl[4]    = 1     Run WrDQ1D - 1d write dq training
            // SequenceCtrl[5]    = 0     RFU, must be zero
            // SequenceCtrl[6]    = 0     RFU, must be zero
            // SequenceCtrl[7]    = 0     RFU, must be zero
            //
            // SequenceCtrl[8]    = 1     Run RdDeskew - Per lane read dq deskew training
            // SequenceCtrl[9]    = 1     Run MxRdLat - Max read latency training
            // SequenceCtrl[10]   = 0     RFU, must be zero
            // SequenceCtrl[11]   = 0     RFU, must be zero
            //
            // SequenceCtrl[12]   = 1     Run LPCA - CA Training
            // SequenceCtrl[13]   = 0     RFU, must be zero
            // SequenceCtrl[14]   = 0     RFU, must be zero
            // SequenceCtrl[15]   = 0     RFU, must be zero
            if(IS_LPDDR4) {
                if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {
                    physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x121f, 0);
                    physetup_set_msg_block (cinit_cfg, i, "Disable2D", 0x1, 0);
                    physetup_set_msg_block (cinit_cfg, i, "CATrainOpt", 0x89, 0);
                }
                else {
                    physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x0001, 0);   //Run DevInit only
                }
            }
            else if(IS_LPDDR5) {
                if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {

                    /* - P80001562-141001*/
                    /* - Disable WrDq training step for PPT2 until fix in firmware 2021.10.*/
#ifdef DWC_FIRMWARE_RID_GE202110
                    physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x121f, 0);
#else
#ifdef DDRCTL_PPT2
                    physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x120f, 0);
#else
                    physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x121f, 0);
#endif// DDRCTL_PPT2
#endif // DWC_FIRMWARE_RID_GE202110

#ifdef DWC_FIRMWARE_RID_GE202006
                    physetup_set_msg_block (cinit_cfg, i, "DisableTrainingLoop", 0x7, 0);
#endif
                    physetup_set_msg_block (cinit_cfg, i, "Disable2D", 0x1, 0);
                    physetup_set_msg_block (cinit_cfg, i, "CATrainOpt", 0x8b, 0);
                }
                else {
                physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x0001, 0);   //Run DevInit only
                }
            }
        } // for num_dch
    } // for num_pstates
    // For LPDDR4 byte mode, X8Mode must be set to 1 in all PStates to avoid the error message
    // from dwc_ddrphy_phyinit_calcMb() function.
#if PHYINIT
    if(IS_LPDDR4 || IS_LPDDR5) {
        if(SPD.sdram_width_bits[0]==8) {
            for(int ii=0;ii<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;ii++) {
                if ((cfg_pstates & 0x1 << ii) == 0) {
                    continue;
                }
                physetup_set_msg_block (cinit_cfg, ii, "X8Mode", 0xf, train_2d);
            }
        // device[0] (rank0, device0) is x16,
        // device[1] (rank1, device0) is x8, 
        // then mixed_mode setting used
        // rank1 is byte_mode (X8Mode=1), 
        // rank0 is standard  (X8Mode=0)
        } else if ((SPD.sdram_width_bits[0]==16) && (SPD.sdram_width_bits[1]==8) && (SPD.num_ranks==2)) {
            for(int ii=0;ii<DWC_DDRPHY_PHYINIT_MAX_NUM_PSTATE;ii++) {
                if ((cfg_pstates & 0x1 << ii) == 0) {
                    continue;
                }
                physetup_set_msg_block (cinit_cfg, ii, "X8Mode", 0xa, train_2d);                
            }
        }
    }
#endif
}

#endif // DDRCTL_LPDDR
