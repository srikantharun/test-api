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
#include "ctrl_words/ddr5/cinit_ddr5_ctrl_words.h"
#include "dwc_ddrctl_cinit_defines.h"

#ifdef DDRCTL_DDR
#ifdef DDR5_PHY

/** @brief Function to call function need when configuring PHYINIT.
 * The follow steps are taken:
 * - calculate some local variables to map to PHYINT requirements.
 * - Setup userInputBasic
 * - Setup userInputAdvanced
 * - Setup userInputSim
*/
void dwc_cinit_phyinit_setuserinput(SubsysHdlr_t *cinit_cfg )
{
  SNPS_TRACE("Entering");
  uint8_t train_2d;
  uint8_t is_2t_timing;
  uint16_t disabled_dbyte;
  uint8_t is_2n_mode;
  uint8_t mr_value;
  uint32_t dram_type,dimm_type, cs_present_cha, cs_present_chb;
  uint32_t num_active_dbyte_dfi0, num_active_dbyte_dfi1, first_pstate;
  uint32_t num_dbytes_per_ch, num_ch, cfg_pstates, num_rank;
  uint32_t mr0[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr1[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr2[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr3[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr4[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr5[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr6[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr8[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr13[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr34[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr35[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr37[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr38[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr39[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr50[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr51[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr52[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t mr2_cwl[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t rcw00[cinit_cfg->num_pstates][cinit_cfg->num_dch], rcw01[cinit_cfg->num_pstates][cinit_cfg->num_dch], rcw11[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint8_t bl[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  cl[cinit_cfg->num_pstates][cinit_cfg->num_dch],rd_preamble_enable[cinit_cfg->num_pstates][cinit_cfg->num_dch],wr_leveling[cinit_cfg->num_pstates][cinit_cfg->num_dch],ddr5_2n_mode[cinit_cfg->num_pstates][cinit_cfg->num_dch],cs_assertion_duration[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  mpsm[cinit_cfg->num_pstates][cinit_cfg->num_dch],dev15_mpsm[cinit_cfg->num_pstates][cinit_cfg->num_dch],internal_wr_timing[cinit_cfg->num_pstates][cinit_cfg->num_dch], refresh_trfc_mode[cinit_cfg->num_pstates][cinit_cfg->num_dch], refresh_rate[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  data_output_disable[cinit_cfg->num_pstates][cinit_cfg->num_dch], pull_up_output_drv_impedance[cinit_cfg->num_pstates][cinit_cfg->num_dch], tdqs_enable[cinit_cfg->num_pstates][cinit_cfg->num_dch], dm_enable[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  pull_down_output_drv_impedance[cinit_cfg->num_pstates][cinit_cfg->num_dch], trtp[cinit_cfg->num_pstates][cinit_cfg->num_dch], wr_recovery[cinit_cfg->num_pstates][cinit_cfg->num_dch], rd_preamble[cinit_cfg->num_pstates][cinit_cfg->num_dch], wr_preamble[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  rd_postamble[cinit_cfg->num_pstates][cinit_cfg->num_dch], wr_postamble[cinit_cfg->num_pstates][cinit_cfg->num_dch], tccd_l[cinit_cfg->num_pstates][cinit_cfg->num_dch],rtt_park[cinit_cfg->num_pstates][cinit_cfg->num_dch],rtt_wr[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  rtt_nom_wr[cinit_cfg->num_pstates][cinit_cfg->num_dch], rtt_nom_rd[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtlon_wr_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtloff_wr_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtlon_rd_nt_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  odtloff_rd_nt_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtlon_wr_nt_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch], odtloff_wr_nt_offset[cinit_cfg->num_pstates][cinit_cfg->num_dch], rd_crc_enable[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  wr_crc_enable_lower_nibble[cinit_cfg->num_pstates][cinit_cfg->num_dch], wr_crc_enable_upper_nibble[cinit_cfg->num_pstates][cinit_cfg->num_dch], wr_crc_error_status[cinit_cfg->num_pstates][cinit_cfg->num_dch], wr_crc_auto_disable_enable[cinit_cfg->num_pstates][cinit_cfg->num_dch],
  wr_crc_auto_disable_status[cinit_cfg->num_pstates][cinit_cfg->num_dch],wr_crc_auto_disable_thre[cinit_cfg->num_pstates][cinit_cfg->num_dch],wr_crc_auto_disable_window[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint8_t ca_rate[cinit_cfg->num_pstates][cinit_cfg->num_dch], sdr_mode[cinit_cfg->num_pstates][cinit_cfg->num_dch], parity_check[cinit_cfg->num_pstates][cinit_cfg->num_dch], alert_n_assertion[cinit_cfg->num_pstates][cinit_cfg->num_dch], alert_n_reenable[cinit_cfg->num_pstates][cinit_cfg->num_dch], latency_adder_nladd[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t wl_adj_start;
  uint32_t wl_adj_end;
  uint32_t enableddq = 0;
    // LRDIMM only
  uint32_t BC0A_data[cinit_cfg->num_pstates][cinit_cfg->num_dch];
  uint32_t F0BC6x_data[cinit_cfg->num_pstates][cinit_cfg->num_dch];

  uint32_t DqsOscRunTimeSel;

  uint8_t is_capar_retry_enable;

  uint8_t DisableRetraining;

  hdlr = cinit_cfg;

  is_2n_mode=0;
  train_2d=0;
  disabled_dbyte = 0;
  is_capar_retry_enable=0;
  //  dwc_ddrphy_phyinit_setDefault(0);


//#############################################################################
//
// Structure for RuntimeConfig options
//
//#############################################################################
if(cinit_cfg->phy_training==DWC_PHY_SKIP_TRAINING) {
  physetup_set_user_input(cinit_cfg, "initCtrl",0xf);
  physetup_set_user_input(cinit_cfg, "skip_train",1);
} else if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {
  physetup_set_user_input(cinit_cfg, "initCtrl",0x0);
  physetup_set_user_input(cinit_cfg, "skip_train",0);
} else if(cinit_cfg->phy_training==DWC_PHY_DEV_INIT) {
  physetup_set_user_input(cinit_cfg, "initCtrl",0x21);
  physetup_set_user_input(cinit_cfg, "skip_train",2);
}

  physetup_set_user_input (cinit_cfg, "pubRev", DWC_DDR5PHY_PUB_RID);
  if(cinit_cfg->phy_training==DWC_PHY_SKIP_TRAINING) {
    physetup_set_user_input (cinit_cfg, "RetEn",1);//JIRA:P80001562-323916
  }
  else {
    physetup_set_user_input (cinit_cfg, "RetEn",0);
  }
  physetup_set_user_input (cinit_cfg, "DMEMLoadPerfEn",0);

  if(IS_RDIMM) {
  dram_type=0x6;
  } else if (IS_LRDIMM) {
  dram_type=0x7;
  } else {
  dram_type=0x5;
  }

    cfg_pstates = 0x0000;
  first_pstate = 0x0;
  switch (cinit_cfg->num_pstates) {
    case 1:
      cfg_pstates = 0x0001;
      break;
    case 2:
      cfg_pstates = 0x0003;
      break;
    case 3:
      cfg_pstates = 0x0007;
      break;  
    default: // 4
      cfg_pstates = 0x000f;
      break;
  }

    physetup_set_user_input (cinit_cfg, "DramType", dram_type);
    physetup_set_user_input (cinit_cfg, "NumPStates", cinit_cfg->num_pstates);
    physetup_set_user_input (cinit_cfg, "Dfi1Exists", cinit_cfg->dfi1_exists);
    physetup_set_user_input(cinit_cfg, "CfgPStates",cfg_pstates);                 //TODO Bug_7504, Comment_17
    physetup_set_user_input(cinit_cfg, "FirstPState",first_pstate);
    physetup_set_user_input(cinit_cfg, "DisablePhyUpdate",0x1);
    // map controller dqsosc_runtime register to PHY encoding
     uint32_t dqsosc_runtime = cinit_cfg->memCtrlr_m.ddr5_mr[0].mr45.osc_run_time;

    if((16 == dqsosc_runtime) || (32 == dqsosc_runtime) || (63 == dqsosc_runtime)) {
      DqsOscRunTimeSel = dqsosc_runtime * 16;

    } else if ((dqsosc_runtime >= 65) && (dqsosc_runtime <= 127)) {
      DqsOscRunTimeSel = 2048;

    } else if ((dqsosc_runtime >= 128) && (dqsosc_runtime <= 191)) {
      DqsOscRunTimeSel = 4096;

    } else if ((dqsosc_runtime >= 192) && (dqsosc_runtime <= 255)) {
      DqsOscRunTimeSel = 8192;

    } else {
      SNPS_ERROR("DQSOSCRUNTIME.dqosc_runtime = %d is not supported by the PHY",dqsosc_runtime );
    }

    if(IS_NODIMM){
     physetup_set_user_input (cinit_cfg, "Nibble_ECC", 0);
     }

    // Disable PHY-initiated retraining
    for(int p=0;p<cinit_cfg->num_pstates;p++) {
        if(p==0) {physetup_set_user_input (cinit_cfg, "DqsOscRunTimeSel[0]",DqsOscRunTimeSel);}
        if(p==1) {physetup_set_user_input (cinit_cfg, "DqsOscRunTimeSel[1]",DqsOscRunTimeSel);}
        if(p==2) {physetup_set_user_input (cinit_cfg, "DqsOscRunTimeSel[2]",DqsOscRunTimeSel);}
        if(p==3) {physetup_set_user_input (cinit_cfg, "DqsOscRunTimeSel[3]",DqsOscRunTimeSel);}
    }

    // PHY-initiated re-training is enabled only for DDR5 PHY training case.
    if ((IS_DDR5) && (cinit_cfg->phy_training == DWC_PHY_TRAINING)) {
        DisableRetraining = 0;    //Enable PPT
    }
    else {
        DisableRetraining = 1;    //Disable PPT
    }
    physetup_set_user_input(cinit_cfg, "DisableRetraining", DisableRetraining);

 #ifdef DDRCTL_DDR_DRAM_ECC_WIDTH_GT_0
    if(cinit_cfg->dfi1_exists){
      if(IS_DUAL_CHAN) {
        num_active_dbyte_dfi0 = DIV_2(cinit_cfg->num_dbytes);
        num_active_dbyte_dfi1 = DIV_2(cinit_cfg->num_dbytes);
	num_dbytes_per_ch = DIV_2(cinit_cfg->num_dbytes);
      } else {
          if(cinit_cfg->ddr5_lock_step_connect_en) {
            num_dbytes_per_ch = DIV_2(cinit_cfg->num_dbytes);
            num_active_dbyte_dfi0 = DIV_2(cinit_cfg->num_dbytes);
            num_active_dbyte_dfi1 = cinit_cfg->num_dbytes - num_active_dbyte_dfi0;
          } else {
            num_dbytes_per_ch = cinit_cfg->num_dbytes;
   #ifdef DDRCTL_DDR_DCH_HBW_1
             num_active_dbyte_dfi0 = cinit_cfg->num_dbytes;
   #else // Not DDRCTL_DDR_DCH_HBW_1
             num_active_dbyte_dfi0 = DIV_2(cinit_cfg->num_dbytes);
   #endif // DDRCTL_DDR_DCH_HBW_1
            num_active_dbyte_dfi1 = 0;
          }
      }
    } else {
      if ((DWC_DDRCTL_NUM_CHANNEL==2) &&(REGB_DDRC_CH0.chctl.dual_channel_en == 0)){
        num_active_dbyte_dfi0 = cinit_cfg->num_dbytes/2;
	num_dbytes_per_ch = cinit_cfg->num_dbytes/2;
      }
      else {
        num_active_dbyte_dfi0 = cinit_cfg->num_dbytes;
	num_dbytes_per_ch = cinit_cfg->num_dbytes;
      }
      num_active_dbyte_dfi1 = 0;
    }
#else
    if(cinit_cfg->dfi1_exists){
      if(IS_DUAL_CHAN) {
        num_active_dbyte_dfi0 = DIV_2(cinit_cfg->num_dbytes);
        num_active_dbyte_dfi1 = DIV_2(cinit_cfg->num_dbytes);
	num_dbytes_per_ch = DIV_2(cinit_cfg->num_dbytes);
  #ifdef DDRCTL_DDR_DCH_HBW_1
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_QUARTER) {
            num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
            num_active_dbyte_dfi1 = DIV_2(num_active_dbyte_dfi1);
        }
  #else // Not DDRCTL_DDR_DCH_HBW_1
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
            num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
            num_active_dbyte_dfi1 = DIV_2(num_active_dbyte_dfi1);
        }
  #endif // DDRCTL_DDR_DCH_HBW_1

      } else {
        num_active_dbyte_dfi0 = DIV_2(cinit_cfg->num_dbytes);
        if(cinit_cfg->ddr5_lock_step_connect_en) {
            num_active_dbyte_dfi1 = cinit_cfg->num_dbytes - num_active_dbyte_dfi0;
        } else {
            num_active_dbyte_dfi1 = 0;
        }
        num_dbytes_per_ch = DIV_2(cinit_cfg->num_dbytes);
  #ifdef DDRCTL_DDR_DCH_HBW_1
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_QUARTER) {
            num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);
        }
  #else // Not DDRCTL_DDR_DCH_HBW_1
        if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF) {
            num_active_dbyte_dfi0 = DIV_2(num_active_dbyte_dfi0);

            if(cinit_cfg->ddr5_lock_step_connect_en) {
                num_active_dbyte_dfi1 = DIV_2(num_active_dbyte_dfi1);
            } 
        }
  #endif // DDRCTL_DDR_DCH_HBW_1

      }
    } else {
          num_dbytes_per_ch = cinit_cfg->num_dbytes;
         if( cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_FULL ) {
             num_active_dbyte_dfi0 = cinit_cfg->num_dbytes;
         } else if(cinit_cfg->memCtrlr_m.sdram_bus_width==DWC_BUSWIDTH_HALF ) {
             num_active_dbyte_dfi0 = DIV_2(cinit_cfg->num_dbytes);
         } else {
             num_active_dbyte_dfi0 = DIV_4(cinit_cfg->num_dbytes);
         }
             num_active_dbyte_dfi1 = 0;
    }
#endif

   #ifdef DDRCTL_DDR_DRAM_ECC_WIDTH_GT_0
     if(IS_UDIMM) {
       enableddq = 0x24;
     } else if((IS_RDIMM || IS_LRDIMM) && cinit_cfg->spdData_m.ddr5_dimm_ch_arch == DATA_CHANNEL_36_BIT) {
       enableddq = 0x24;
     } else {
       enableddq = 0x28;
     }
   #else
       enableddq = 0x20;
   #endif

    #ifdef DWC_DDR5PHY_NUM_CHANNELS_2
     num_ch = 2;
   #else
     num_ch = 1;
   #endif

  #ifdef DWC_DDR5PHY_NUM_RANKS_4
     num_rank = 4;
  #else
    #ifdef DWC_DDR5PHY_NUM_RANKS_2
       num_rank = 2;
    #else
     num_rank = 1;
    #endif
  #endif

    physetup_set_user_input (cinit_cfg, "NumActiveDbyteDfi0", num_active_dbyte_dfi0);
    physetup_set_user_input (cinit_cfg, "NumActiveDbyteDfi1", num_active_dbyte_dfi1);
    physetup_set_user_input (cinit_cfg, "NumRank_dfi0",cinit_cfg->spdData_m.num_ranks);
    if(IS_DUAL_CHAN) {
      physetup_set_user_input (cinit_cfg, "NumRank_dfi1",cinit_cfg->spdData_m.num_ranks);
    } else {
      if(cinit_cfg->ddr5_lock_step_connect_en) {
        physetup_set_user_input (cinit_cfg, "NumRank_dfi1",cinit_cfg->spdData_m.num_ranks);
      } else {
        physetup_set_user_input (cinit_cfg, "NumRank_dfi1",0);
      }
    }


    physetup_set_user_input (cinit_cfg, "NumRank", num_rank);
    physetup_set_user_input (cinit_cfg, "NumDbytesPerCh", num_dbytes_per_ch);
    physetup_set_user_input (cinit_cfg, "NumCh", num_ch);

    if(IS_UDIMM ) {dimm_type=0;}
    if(IS_RDIMM ) {dimm_type=2;}
    if(IS_LRDIMM) {dimm_type=3;}
    if(IS_NODIMM) {dimm_type=4;}
    physetup_set_user_input (cinit_cfg, "DimmType", dimm_type);

   #ifdef DWC_PHYINIT_RID_GE202211
    physetup_set_user_input (cinit_cfg, "DramDataWidth[0]", cinit_cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input (cinit_cfg, "DramDataWidth[1]", cinit_cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input (cinit_cfg, "DramDataWidth[2]", cinit_cfg->spdData_m.sdram_width_bits[0]);
    physetup_set_user_input (cinit_cfg, "DramDataWidth[3]", cinit_cfg->spdData_m.sdram_width_bits[0]);
   #else
    physetup_set_user_input (cinit_cfg, "DramDataWidth", cinit_cfg->spdData_m.sdram_width_bits[0]);
   #endif

    for(int p=0;p<cinit_cfg->num_pstates;p++) {
        uint8_t freq_ratio = (ddrctl_sw_get_ratio(cinit_cfg, p) == DWC_RATIO_1_2) ? 1 : 2;
        if(p==0) {physetup_set_user_input (cinit_cfg, "DfiFreqRatio[0]",freq_ratio);}
        if(p==1) {physetup_set_user_input (cinit_cfg, "DfiFreqRatio[1]",freq_ratio);}
        if(p==2) {physetup_set_user_input (cinit_cfg, "DfiFreqRatio[2]",freq_ratio);}
        if(p==3) {physetup_set_user_input (cinit_cfg, "DfiFreqRatio[3]",freq_ratio);}
    }

    for(int p=0;p<cinit_cfg->num_pstates;p++) {
    // VIP interprets 333 as 6000 Mbps, PHY as 6006 Mbps, For RD CRC - CL is increased by 2 ifMbps > 6000, increase by 1 to align VIP + PHY
    // VIP interprets 312 as 6400 Mbps, PHY as 6410 Mbps, For RD CRC - CL is increased by 2 ifMbps < 6400, increase by 1 to align VIP + PHY
    uint32_t tck_ps;
    if ((cinit_cfg->spdData_m.tck_ps[p] == 333) || (cinit_cfg->spdData_m.tck_ps[p] == 312) || (cinit_cfg->spdData_m.tck_ps[p] == 238) || (cinit_cfg->spdData_m.tck_ps[p] == 227)) {
        tck_ps=cinit_cfg->spdData_m.tck_ps[p] + 1;
    } else {
       tck_ps=cinit_cfg->spdData_m.tck_ps[p];
    }

        uint32_t freq=CEIL(1000000,tck_ps);
        if(p==0) {physetup_set_user_input(cinit_cfg, "Frequency[0]",freq);}
        if(p==1) {physetup_set_user_input(cinit_cfg, "Frequency[1]",freq);}
        if(p==2) {physetup_set_user_input(cinit_cfg, "Frequency[2]",freq);}
        if(p==3) {physetup_set_user_input(cinit_cfg, "Frequency[3]",freq);}
    }
    physetup_set_user_input(cinit_cfg, "PllBypass[0]", REGB_DDRC_CH0.mstr0.dll_off_mode);
    physetup_set_user_input(cinit_cfg, "PllBypass[1]", 0);  // TODO
    physetup_set_user_input(cinit_cfg, "PllBypass[2]", 0);  // TODO
    physetup_set_user_input(cinit_cfg, "PllBypass[3]", 0);  // TODO


  if(IS_RDIMM || IS_LRDIMM) {
    // only implement disable EnTdqs2dqTrackingTg*/EnRxDqsTracking*
    // in following:
    // - DDR5
    // - RDIMM or LRDIMM
    // - if any channel has capar_retry_enable=1
    for (uint32_t jj=0; jj<cinit_cfg->num_dch; jj++) {
      if (cinit_cfg->memCtrlr_m.static_cfg.capar_retry_enable[jj] == 1) {
        is_capar_retry_enable = 1;
      }
    }

    if(is_capar_retry_enable) {
      // see Mantis 62220/59229
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg0[0]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg1[0]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg2[0]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg3[0]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg0[1]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg1[1]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg2[1]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg3[1]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg0[2]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg1[2]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg2[2]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg3[2]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg0[3]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg1[3]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg2[3]", 0);
      physetup_set_user_input(cinit_cfg, "EnTdqs2dqTrackingTg3[3]", 0);
      physetup_set_user_input(cinit_cfg, "EnRxDqsTracking[0]", 0);
      physetup_set_user_input(cinit_cfg, "EnRxDqsTracking[1]", 0);
      physetup_set_user_input(cinit_cfg, "EnRxDqsTracking[2]", 0);
      physetup_set_user_input(cinit_cfg, "EnRxDqsTracking[3]", 0);
    }
    SNPS_LOG("is_capar_retry_enable=%0u",is_capar_retry_enable);

  }

    physetup_set_user_input (cinit_cfg, "MemAlertEn",1); // allow dfi_alert_n to be driven to the controller
    physetup_set_user_input (cinit_cfg, "EnableMAlertAsync",REGB_DDRC_CH0.crcparctl1.dfi_alert_async_mode);
    physetup_set_user_input (cinit_cfg, "DisablePmuEcc",1);//disabled the SRAM ECC feature temporarily
    if(IS_RDIMM || IS_LRDIMM) {
      if( cinit_cfg->memCtrlr_m.ddr5_mr[0].mr2.ddr5_2n_mode ) { // 1N mode
        is_2n_mode=0;
      }
      else { // 2N mode
        is_2n_mode=1;
      }
      SNPS_LOG("is_2n_mode=%0u",is_2n_mode);
     if(IS_RDIMM) {
      for(int p=0;p<cinit_cfg->num_pstates;p++) {
        // CASE 01050020 From VIP team tSTAOFF_ps = tPDM_ps + 0.5*tCK_ps
        int ddr5_rcd_tstaoff_ps;
            ddr5_rcd_tstaoff_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tpdm_ps + DIV_2(cinit_cfg->spdData_m.tck_ps[p]) + 2; // Adjust for TxDly
            SNPS_LOG("ddr5_rcd_tstaoff_ps=%0u",ddr5_rcd_tstaoff_ps);

        if(p==0) {physetup_set_user_input(cinit_cfg, "tSTAOFF[0]",ddr5_rcd_tstaoff_ps);}
        if(p==1) {physetup_set_user_input(cinit_cfg, "tSTAOFF[1]",ddr5_rcd_tstaoff_ps);}
        if(p==2) {physetup_set_user_input(cinit_cfg, "tSTAOFF[2]",ddr5_rcd_tstaoff_ps);}
        if(p==3) {physetup_set_user_input(cinit_cfg, "tSTAOFF[3]",ddr5_rcd_tstaoff_ps);}
      }
    #ifndef DWC_PHYINIT_RID_GE202211
      for(int p=0;p<cinit_cfg->num_pstates;p++) {
        int ddr5_rcd_tpdm_ps=cinit_cfg->timingParams_m[p][0].ddr5_rcd_tpdm_ps;
        if(p==0) {physetup_set_user_input(cinit_cfg, "tPDM[0]",ddr5_rcd_tpdm_ps);}
        if(p==1) {physetup_set_user_input(cinit_cfg, "tPDM[1]",ddr5_rcd_tpdm_ps);}
        if(p==2) {physetup_set_user_input(cinit_cfg, "tPDM[2]",ddr5_rcd_tpdm_ps);}
        if(p==3) {physetup_set_user_input(cinit_cfg, "tPDM[3]",ddr5_rcd_tpdm_ps);}
      }
    #endif
     } // IS_RDIMM

    }
    /// Work around for PHY get wrong read data in some case
      uint32_t tck_ps=cinit_cfg->spdData_m.tck_ps[0];
      int tDQSCK_ps; // Adjust for RxDly
      if(tck_ps >= 625 ){
        tDQSCK_ps = 2;
      }
      else {
        tDQSCK_ps = 1;
      }
      physetup_set_user_input(cinit_cfg, "tDQSCK", tDQSCK_ps);/// Work around for PHY get wrong read data in some case
    // align tDQS2DQ with value set in the VIP
    SNPS_LOG("Setting tDQS2DQ  to %0ups", cinit_cfg->timingParams_m[0][0].ddr5_tdqs2dq_ps);
    physetup_set_user_input(cinit_cfg, "tDQS2DQ", cinit_cfg->timingParams_m[0][0].ddr5_tdqs2dq_ps);
    physetup_set_user_input(cinit_cfg, "PHY_tDQS2DQ", 238);//JiraP80001562-286391


  if(IS_LRDIMM) {
    int ddr5_rcd_tstaoff_ps;

    for(int p=0; p<cinit_cfg->num_pstates; p++) {
       if(is_2n_mode) {
         #ifdef DWC_PHYINIT_RID_GE202008
            ddr5_rcd_tstaoff_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tstaoff_ps + 2 - DIV_2(cinit_cfg->spdData_m.tck_ps[p]); // -1UI for SDR2 mode as a workaround
         #else
            ddr5_rcd_tstaoff_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tstaoff_ps + 2; // Adjust for TxDly
         #endif
        } else {
            //ddr5_rcd_tstaoff_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tstaoff_ps + 2 + DIV_2(cinit_cfg->spdData_m.tck_ps[p]); // Adjust for TxDly
	    ddr5_rcd_tstaoff_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tstaoff_ps + 2; // Adjust for TxDly
        }

      if(p==0) {physetup_set_user_input(cinit_cfg, "tSTAOFF[0]",ddr5_rcd_tstaoff_ps);}
      if(p==1) {physetup_set_user_input(cinit_cfg, "tSTAOFF[1]",ddr5_rcd_tstaoff_ps);}
      if(p==2) {physetup_set_user_input(cinit_cfg, "tSTAOFF[2]",ddr5_rcd_tstaoff_ps);}
      if(p==3) {physetup_set_user_input(cinit_cfg, "tSTAOFF[3]",ddr5_rcd_tstaoff_ps);}
    }


        // set tPDM/tPDM_Rd id DDR5 LRDIMM
	    int ddr5_rcd_tpdm_rd_ps, ddr5_rcd_tpdm_wr_ps;
        for(int p=0; p<cinit_cfg->num_pstates; p++) {
           ddr5_rcd_tpdm_rd_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tpdm_rd_ps;
           ddr5_rcd_tpdm_wr_ps = cinit_cfg->timingParams_m[p][0].ddr5_rcd_tpdm_wr_ps;
           if((is_2n_mode)&& (cinit_cfg->ddr5_cw.rw00.sdr_mode==0)) {
              ddr5_rcd_tpdm_rd_ps = ddr5_rcd_tpdm_rd_ps + cinit_cfg->spdData_m.tck_ps[p];
              ddr5_rcd_tpdm_wr_ps = ddr5_rcd_tpdm_wr_ps - cinit_cfg->spdData_m.tck_ps[p];
           }
       #ifndef DWC_PHYINIT_RID_GE202211
           if(p==0) {
               physetup_set_user_input(cinit_cfg, "tPDM[0]",ddr5_rcd_tpdm_wr_ps);
           }
           if(p==1) {
               physetup_set_user_input(cinit_cfg, "tPDM[1]",ddr5_rcd_tpdm_wr_ps);
           }
           if(p==2) {
               physetup_set_user_input(cinit_cfg, "tPDM[2]",ddr5_rcd_tpdm_wr_ps);
           }
           if(p==3) {
               physetup_set_user_input(cinit_cfg, "tPDM[3]",ddr5_rcd_tpdm_wr_ps);
            }
       #endif
        } // for p

  }


  // put the mode register settings into a format suitable for dwc_ddrphy_physetup_set_user_input
  for (uint32_t ii=0; ii<cinit_cfg->num_pstates; ii++) {
    for (uint32_t jj=0; jj<cinit_cfg->num_dch; jj++) {
          SNPS_LOG("dwc_cinit_phyinit_setuserinput: pstate = %d IS_DDR5 = %d", ii, IS_DDR5);
          ddr5_mode_registers_t* mr = &(cinit_cfg->memCtrlr_m.ddr5_mr[ii]);
          ddr5_control_words_t*  rcw= &(cinit_cfg->ddr5_cw);
          bl[ii][jj]= mr->mr0.burst_length;
          cl[ii][jj]= mr->mr0.cl;
          mr0[ii][jj] = (bl[ii][jj]&0x3) | ((cl[ii][jj]&0x1f)<<2);
          rd_preamble_enable[ii][jj]= mr->mr2.rd_preamble_enable;
          wr_leveling[ii][jj]= mr->mr2.wr_leveling;
          ddr5_2n_mode[ii][jj]=mr->mr2.ddr5_2n_mode;
          cs_assertion_duration[ii][jj] = (DisableRetraining == 0)? 1 : mr->mr2.cs_assertion_duration; //CS assertion single cycle for MPC command when re-training is enabled, JIRA:P80001562-362434
          SNPS_LOG("DisableRetraining = %0d, mr2.cs_assertion_duration[%0d][%0d] = %0d",DisableRetraining,ii,jj,cs_assertion_duration[ii][jj] );
          mpsm[ii][jj]= mr->mr2.mpsm;
          dev15_mpsm[ii][jj] = mr->mr2.dev15_mpsm;
          internal_wr_timing[ii][jj] = 1;//enable internal write timing
          //mr3[ii][jj]= ((dll_reset[ii][jj]&0x1)<<7) | ((dll_enable[ii][jj]&0x1)<<6) | ((cs_assertion_duration[ii][jj]&0x1)<<2) | ((mpsm[ii][jj]&0x1)<<1);
          mr2[ii][jj]= ((internal_wr_timing[ii][jj]&0x1)<<7) | ((dev15_mpsm[ii][jj]&0x1)<<5) | ((cs_assertion_duration[ii][jj]&0x1)<<4) | ((mpsm[ii][jj]&0x1)<<3) | ((ddr5_2n_mode[ii][jj]&0x01)<<2) | ((wr_leveling[ii][jj]&0x1)<<1) | ((rd_preamble_enable[ii][jj]&0x1));
          refresh_trfc_mode[ii][jj]= mr->mr4.refresh_trfc_mode;
          refresh_rate[ii][jj]= mr->mr4.refresh_rate;
          mr4[ii][jj]= ((refresh_trfc_mode[ii][jj]&0x1)<<4) | (refresh_rate[ii][jj]&0x7);
          data_output_disable[ii][jj]= mr-> mr5.data_output_disable;
          pull_up_output_drv_impedance[ii][jj]= mr->mr5.pull_up_output_drv_impedance;
          tdqs_enable[ii][jj]= mr-> mr5.tdqs_enable;
          dm_enable[ii][jj]= mr-> mr5.dm_enable;
          pull_down_output_drv_impedance[ii][jj]= mr-> mr5.pull_down_output_drv_impedance;
          mr5[ii][jj]= (data_output_disable[ii][jj]&0x1) | ((pull_up_output_drv_impedance[ii][jj]&0x3)<<1) | ((tdqs_enable[ii][jj]&0x1)<<4) | ((dm_enable[ii][jj]&0x1)<<5) | ((pull_down_output_drv_impedance[ii][jj]&0x3)<<6);
          trtp[ii][jj]= mr-> mr6.trtp;
          wr_recovery[ii][jj]= mr-> mr6.wr_recovery;
          mr6[ii][jj]= ((trtp[ii][jj]&0xf)<<4) | (wr_recovery[ii][jj]&0xf);
          rd_preamble[ii][jj]=mr->mr8.rd_preamble;
          wr_preamble[ii][jj]=mr->mr8.wr_preamble;
          rd_postamble[ii][jj]=mr->mr8.rd_postamble;
          wr_postamble[ii][jj]=mr->mr8.wr_postamble;
          mr8[ii][jj]= (rd_preamble[ii][jj]&0x7) | ((wr_preamble[ii][jj]&0x3)<<3) | ((rd_postamble[ii][jj]&0x1)<<6) | ((wr_postamble[ii][jj]&0x1)<<7);
          tccd_l[ii][jj]=mr->mr13.tccd_l;
          mr13[ii][jj]= tccd_l[ii][jj]&0xf;
          rtt_park[ii][jj]=mr->mr34.rtt_park;
          rtt_wr[ii][jj]= mr->mr34.rtt_wr;
          mr34[ii][jj]= (rtt_wr[ii][jj]&0x7)<<3 | (rtt_park[ii][jj]&0x7);
          rtt_nom_wr[ii][jj]=mr->mr35.rtt_nom_wr;
          rtt_nom_rd[ii][jj]=mr->mr35.rtt_nom_rd;
          mr35[ii][jj]= (rtt_nom_wr[ii][jj]&0x7) | ((rtt_nom_rd[ii][jj]&0x7)<<3);
          odtlon_wr_offset[ii][jj]=mr->mr37.odtlon_wr_offset;
          odtloff_wr_offset[ii][jj]=mr->mr37.odtloff_wr_offset;
          mr37[ii][jj]= (odtlon_wr_offset[ii][jj]&0x7) | ((odtloff_wr_offset[ii][jj]&0x7)<<3);
          odtlon_wr_nt_offset[ii][jj]= mr->mr38.odtlon_wr_nt_offset;
          odtloff_wr_nt_offset[ii][jj]= mr->mr38.odtloff_wr_nt_offset;
          mr38[ii][jj]=(odtlon_wr_nt_offset[ii][jj]&0x7) | ((odtloff_wr_nt_offset[ii][jj]&0x7)<<3);
          odtlon_rd_nt_offset[ii][jj]= mr->mr39.odtlon_rd_nt_offset;
          odtloff_rd_nt_offset[ii][jj]=mr->mr39.odtloff_rd_nt_offset;
          mr39[ii][jj]= (odtlon_rd_nt_offset[ii][jj]&0x7) | ((odtloff_rd_nt_offset[ii][jj]&0x7)<<3);
          rd_crc_enable[ii][jj]= mr->mr50.rd_crc_enable;
          wr_crc_enable_lower_nibble[ii][jj]= mr->mr50.wr_crc_enable_lower_nibble;
          wr_crc_enable_upper_nibble[ii][jj]= mr->mr50.wr_crc_enable_upper_nibble;
          wr_crc_error_status[ii][jj]= mr->mr50.wr_crc_error_status;
          wr_crc_auto_disable_enable[ii][jj]= mr->mr50.wr_crc_auto_disable_enable;
          wr_crc_auto_disable_status[ii][jj]= mr->mr50.wr_crc_auto_disable_status;
          mr50[ii][jj]=(rd_crc_enable[ii][jj]&0x1) | ((wr_crc_enable_lower_nibble[ii][jj]&0x1)<<1) | ((wr_crc_enable_upper_nibble[ii][jj]&0x1)<<2) | ((wr_crc_error_status[ii][jj]&0x1)<<3) | ((wr_crc_auto_disable_enable[ii][jj]&0x1)<<4) | ((wr_crc_auto_disable_status[ii][jj]&0x1)<<5);
      wr_crc_auto_disable_thre[ii][jj]= mr->mr51.wr_crc_auto_disable_thre;
      mr51[ii][jj]= wr_crc_auto_disable_thre[ii][jj]&0x7f;
      wr_crc_auto_disable_window[ii][jj]= mr->mr52.wr_crc_auto_disable_window;
      mr52[ii][jj]= wr_crc_auto_disable_window[ii][jj]&0x7f;
         ca_rate[ii][jj]= rcw->rw00.ca_rate;
         sdr_mode[ii][jj]= rcw->rw00.sdr_mode;
         if (IS_RDIMM || IS_LRDIMM){
            rcw00[ii][jj] = (ca_rate[ii][jj]&0x1) | ((sdr_mode[ii][jj]&0x1)<<1);
         } else {
            rcw00[ii][jj] = ca_rate[ii][jj]&0x1;
         }

         parity_check[ii][jj]= rcw->rw01.parity_check;
         alert_n_assertion[ii][jj]= rcw->rw01.alert_n_assertion;
         alert_n_reenable[ii][jj]= rcw->rw01.alert_n_reenable;
         rcw01[ii][jj] = (parity_check[ii][jj]&0x1) | ((alert_n_assertion[ii][jj]&0x1)<<6) | ((alert_n_reenable[ii][jj]&0x1)<<7);
         latency_adder_nladd[ii][jj] = rcw->rw11.latency_adder_nladd_to_all_dram_cmd;
         rcw11[ii][jj] = latency_adder_nladd[ii][jj]&0xf;
        switch (wr_preamble[ii][jj] ) {
          case 1 : wl_adj_start = 96; break;
          case 2 : wl_adj_start = 160; break;
          case 3 : wl_adj_start = 288; break;
          default :
                    wl_adj_start = 0;
                    break;
        }
        switch (wr_preamble[ii][jj] ) {
          case 1 : wl_adj_end = 160; break;
          case 2 : wl_adj_end = 224; break;
          case 3 : wl_adj_end = 352; break;
          default :
                    wl_adj_end = 0;
                    break;
        }


  } // jj -> dch
  } // ii -> pstates


  if(IS_UDIMM) {dimm_type=0;}
  if(IS_RDIMM) {dimm_type=2;}
  if(IS_LRDIMM) {dimm_type=3;}
  if(IS_NODIMM) {dimm_type=4;}
  // When MEMC_SIDEBAND_ECC was defined, it indicates the ECC was enabled.
  // ECC byte always use the most significant byte, so both of num_dbyte and enabled_dq should been considered as FBW
  // For HBW/QBW, disabled_dbyte should be used to skip the un-connected dbytes.
  // But, for SNPS_DIMM, an extra define VIRL_DIMM_ECC_MODE_0 will be used to indicate the ECC device won't be used.
  // So, when VIRL_DIMM_ECC_MODE_0 is defined, the num_dbyte shouldn't take into account ECC width.



  if(cinit_cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_QUARTER){
   #ifdef DWC_PHYINIT_RID_GE202211
      disabled_dbyte = 0x18c;
   #else
      disabled_dbyte = 0xcc;
   #endif
  } else if(cinit_cfg->memCtrlr_m.sdram_bus_width == DWC_BUSWIDTH_HALF){
     if(MEMC_DRAM_DATA_WIDTH == 32){
     #ifdef DWC_PHYINIT_RID_GE202211
       disabled_dbyte = 0x18c;
     #else
       disabled_dbyte = 0xcc;
     #endif
      }
  }

  //#############################################################################
  //
  // Structure for basic (mandatory) user inputs
  //
  //#############################################################################

   if(cinit_cfg->spdData_m.num_ranks==4) {
    cs_present_cha=0xf;
  } else if(cinit_cfg->spdData_m.num_ranks==2) {
      if(IS_RDIMM || IS_LRDIMM) {
        if(cinit_cfg->spdData_m.num_ranks_per_dimm==1){ // 1 rank rdimm *2
          cs_present_cha=0x5;
        } else {
          cs_present_cha=0x3;
        }
      } else if (IS_UDIMM) {
        if(cinit_cfg->spdData_m.num_ranks_per_dimm==1){ // 1 rank udimm *2
          cs_present_cha=0x5;
        } else {
          cs_present_cha=0x3;
        }
      } else { // NODIMM
        cs_present_cha=0x3;
      }
  }
  else { // 1 rank
    if(IS_DDR5 && (IS_RDIMM || IS_LRDIMM)) {
      cs_present_cha=0x1;
    } else {
      cs_present_cha=0x1;
    }
  }

  if(IS_DUAL_CHAN || (cinit_cfg->ddr5_lock_step_connect_en)){
    if(cinit_cfg->spdData_m.num_ranks==4) {
      cs_present_chb=0xf;
    } else if(cinit_cfg->spdData_m.num_ranks==2) {
        if(IS_RDIMM || IS_LRDIMM) {
          if(cinit_cfg->spdData_m.num_ranks_per_dimm==1){ // 1 rank rdimm *2
            cs_present_chb=0x5;
          } else {
            cs_present_chb=0x3;
          }
        } else if (IS_UDIMM) {
          if(cinit_cfg->spdData_m.num_ranks_per_dimm==1){ // 1 rank udimm *2
            cs_present_chb=0x5;
          } else {
            cs_present_chb=0x3;
          }
        } else { // NODIMM
          cs_present_chb=0x3;
        }
    }
    else { // 1 rank
      if(IS_DDR5 && (IS_RDIMM || IS_LRDIMM)) {
        cs_present_chb=0x1;
      } else {
        cs_present_chb=0x1;
      }
    }
  } else {
     cs_present_chb=0;
  }

//#############################################################################
//
// Structure for advanced (optional) user inputs
// - if user does not enter a value for these parameters, a PHY recommended or
//   default value will be used
//
//#############################################################################



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
  uint32_t msgmisc;
  msgmisc = 0;
  if(cinit_cfg->use_jedec_init==0) { msgmisc |= 1 << 1; }
  msgmisc |= 1 << 2;
#ifdef UMCTL2_SHARED_AC
  msgmisc |= 1 << 6;
#endif

  uint32_t d5misc;
  d5misc = 1;//PHY internal registers control memreset during training, and also after training
  d5misc |= 1 << 2;//Use_back2back_MRR
  d5misc |= 1 << 6;//Train also CK ANIB delay during CS/CA training

  for(int i=0;i<cinit_cfg->num_pstates;i++) {
    for(int j=0;j<1;j++) {  // Hardcode 1 as PHY supports only 1 channel
      physetup_set_msg_block (cinit_cfg, i, "MsgMisc", msgmisc, train_2d);
      physetup_set_msg_block (cinit_cfg, i, "HdtCtrl",cinit_cfg->HdtCtrl , train_2d); // Stage completion
      physetup_set_msg_block (cinit_cfg, i, "DFIMRLMargin", 0x2, train_2d);
      physetup_set_msg_block (cinit_cfg, i, "D5Misc", d5misc, train_2d);
      physetup_set_msg_block (cinit_cfg, i, "DRAMFreq",(CEIL(2000000, cinit_cfg->spdData_m.tck_ps[i] )) , train_2d);
      physetup_set_msg_block (cinit_cfg, i, "DisabledDbyte", disabled_dbyte, train_2d);
      physetup_set_msg_block (cinit_cfg, i, "WL_ADJ_START", wl_adj_start, train_2d);
      physetup_set_msg_block (cinit_cfg, i, "WL_ADJ_END", wl_adj_end, train_2d);
      physetup_set_msg_block (cinit_cfg, i, "EnabledDQsChA", enableddq, train_2d);
      //JIRA: P80001562-379470 For single DFI channel, EnabledDQsChB and CsPresentChB shoule be 0x0
      if (IS_DUAL_CHAN) {
        physetup_set_msg_block (cinit_cfg, i, "EnabledDQsChB", enableddq, train_2d);
      } else {
        physetup_set_msg_block (cinit_cfg, i, "EnabledDQsChB", 0x0, train_2d);
      }
      physetup_set_msg_block (cinit_cfg, i, "MR0_A0", (mr0[i][j] & 0xffff), 0);
      #ifdef DWC_PHYINIT_RID_GE202001
      physetup_set_msg_block (cinit_cfg, i, "MR2_A0", (mr2[i][j] & 0xffff), 0);
      #endif
      physetup_set_msg_block (cinit_cfg, i, "MR4_A0", (mr4[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR5_A0", (mr5[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR6_A0", (mr6[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR8_A0", (mr8[i][j] & 0xffff), 0);
      #ifdef DWC_PHYINIT_RID_GE202001
      physetup_set_msg_block (cinit_cfg, i, "MR13_A0", (mr13[i][j] & 0xffff), 0);
      #endif
      physetup_set_msg_block (cinit_cfg, i, "MR34_A0", (mr34[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR35_A0", (mr35[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR37_A0", (mr37[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR38_A0", (mr38[i][j] & 0xffff), 0);

      physetup_set_msg_block (cinit_cfg, i, "MR39_A0", (mr39[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR50_A0", (mr50[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR51_A0", (mr51[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "MR52_A0", (mr52[i][j] & 0xffff), 0);
      physetup_set_msg_block (cinit_cfg, i, "UseBroadcastMR", 1, 0);

      /*Jira P80001562-309341, Case 01440643, DDR5 UDIMM/NODIMM CA training issue, For 3DS or 64Gb devices, set CATrainOpt[4]=0*/
      if (cinit_cfg->spdData_m.cid_width[0] > 0) {   // 3DS
          physetup_set_msg_block(cinit_cfg, i, "CATrainOpt", 0xc, 0);
          SNPS_LOG("3DS Memory, cinit_cfg->spdData_m.cid_width[0]=%0d",cinit_cfg->spdData_m.cid_width[0] );
      }
      else { // non-3DS
          if ( IS_DENS_64GBIT(0) ) {  // Density 64Gb
               physetup_set_msg_block(cinit_cfg, i, "CATrainOpt", 0xc, 0);
               SNPS_LOG("cinit_cfg->spdData_m.cid_width[0]=%0d",cinit_cfg->spdData_m.cid_width[0] );
               SNPS_LOG("Density 64Gb, DWC_DEN64G=65536, dram_density=%0d",cinit_cfg->spdData_m.sdram_capacity_mbits[0] );
          }
          else { // Other density
               physetup_set_msg_block(cinit_cfg, i, "CATrainOpt", 0x1c, 0);
               SNPS_LOG("cinit_cfg->spdData_m.cid_width[0]=%0d",cinit_cfg->spdData_m.cid_width[0] );
               SNPS_LOG("Density not 64Gb, DWC_DEN64G=65536, dram_density=%0d",cinit_cfg->spdData_m.sdram_capacity_mbits[0] );
          }
      }

      physetup_set_msg_block (cinit_cfg, i, "RX2D_TrainOpt", 0x62, 0);
      physetup_set_msg_block (cinit_cfg, i, "TX2D_TrainOpt", 0x62, 0);
      physetup_set_msg_block (cinit_cfg, i, "CsPresentChA", cs_present_cha, 0);
      physetup_set_msg_block (cinit_cfg, i, "CsPresentChB", cs_present_chb, 0);
      if (IS_RDIMM || IS_LRDIMM) {
        mr_value = ddrctl_sw_get_ddr5_ctrl_word(cinit_cfg, i, 0x05);
        physetup_set_msg_block (cinit_cfg, i, "RCW00_ChA_D0", (rcw00[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW00_ChA_D1", (rcw00[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW00_ChB_D0", (rcw00[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW00_ChB_D1", (rcw00[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW05_ChA_D0", mr_value, 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW05_ChA_D1", mr_value, 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW05_ChB_D0", mr_value, 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW05_ChB_D1", mr_value, 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW11_ChA_D0", (rcw11[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW11_ChA_D1", (rcw11[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW11_ChB_D0", (rcw11[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW11_ChB_D1", (rcw11[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW01_ChA_D0", (rcw01[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW01_ChA_D1", (rcw01[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW01_ChB_D0", (rcw01[i][j] & 0xffff), 0);
        physetup_set_msg_block (cinit_cfg, i, "RCW01_ChB_D1", (rcw01[i][j] & 0xffff), 0);
      }
       if (IS_LRDIMM) {
          //DDR5 LRDIMM 1D
           if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {
             physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0xbe1f, 0);
           } else {
             physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x0001, 0);     //Run DevInit only
           }
      }  else {
          if(cinit_cfg->phy_training==DWC_PHY_TRAINING) {
              physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x821f, 0);
          } else {
              physetup_set_msg_block (cinit_cfg, i, "SequenceCtrl", 0x0001, 0);     //Run DevInit only
          }
      }

    } // for num_dch
  } // for num_pstates

}

#endif //DDRCTL_DDR
#endif //DDR5_PHY
