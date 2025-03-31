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
#include "dwc_ddrctl_cinit_ddr54_dfi_timings.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_defines.h"


/** @brief function for DDR54 PHY DFI timings */
void cinit_cal_ddr54_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n)
{
#ifdef DDRCTL_DDR
    uint32_t DFI_RL_SUB = 0, DFI_WL_SUB = 0, trddata_en_pipe, tphy_wrlat_pipe;
    uint8_t ddr4_rcd_latency_adder_nladd_to_all_dram_cmd;
    uint32_t dfi_t_rddata_en_int, dfi_tphy_wrlat_int;
    uint32_t ratio;
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t freq_mhz = CEIL(1000000,tck_ps);

    ratio = ddrctl_sw_get_ratio_factor(hdlr, p);

#ifdef CINIT_DDR5
    uint32_t dx_in_pipe;
    uint32_t ac_in_pipe;

	if (IS_DDR5) {
	  if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
	    DFI_RL_SUB = 13;
            DFI_WL_SUB = 13;
	    } else {
	#if defined(DWC_PHYINIT_RID_GE202008_exclude)
		#if defined(DWC_PUB_RID_GE410)
			DFI_RL_SUB = 13;
		#elif defined(DWC_PUB_RID_GE340)
			DFI_RL_SUB = 13;
		#else
			DFI_RL_SUB = 9;
		#endif
	#else
		DFI_RL_SUB = 9;
	#endif
#ifdef DWC_PUB_RID_GE330
        DFI_WL_SUB = 13;
#else /* DWC_PUB_RID_GE330 */
        DFI_WL_SUB = 9;
#endif /* DWC_PUB_RID_GE330 */
        }
    }
#endif /* CINIT_DDR5 */
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        DFI_RL_SUB = 5;
        DFI_WL_SUB = 5;
    }
#endif /* CINIT_DDR4 */


    dfi_t_rddata_en_int = PRE_CFG.cl[p] + SPD.tAL - DFI_RL_SUB;     //for 2n mode, +1 (required by the PHY databook) has been considered by the controller RTL, there is no need to add one here

    dfi_tphy_wrlat_int = PRE_CFG.cwl_x[p] + SPD.tAL - DFI_WL_SUB;	//for 2n mode, +1 (required by the PHY databook) has been considered by the controller RTL, there is no need to add one here

#ifdef CINIT_DDR5
    if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
#ifdef DWC_PHYINIT_RID_GE202211
        if (ratio==2) {
            if ((tck_ps>=312) && (tck_ps<476)) {
                dx_in_pipe = ratio*3;
                ac_in_pipe = ratio*1;
            } else {
                dx_in_pipe = ratio*1;
                ac_in_pipe = ratio*0;
            }
        } else {
            if ((tck_ps>=227) && (tck_ps<625)) {
                dx_in_pipe = ratio*1;
                ac_in_pipe = ratio*0;
            } else {
                dx_in_pipe = ratio*0;
                ac_in_pipe = ratio*0;
            }
        }
#else
        dx_in_pipe = (freq_mhz>ratio*1200) ? ratio*3 : ratio*1;
        ac_in_pipe = (freq_mhz>ratio*1200) ? ratio*1 : ratio*0;
#endif
    } else {

        dx_in_pipe = 0;
        ac_in_pipe = 0;
    }
#endif /* CINIT_DDR5 */

    if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
        trddata_en_pipe = ratio * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_rd);
        tphy_wrlat_pipe = ratio * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_wr);
    } else {
        trddata_en_pipe = 2 * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_rd);
        tphy_wrlat_pipe = 2 * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_wr);
    }


#ifdef CINIT_DDR4
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

    if (IS_DDR4 && (IS_RDIMM || IS_LRDIMM))
        ddr4_rcd_latency_adder_nladd_to_all_dram_cmd = hdlr->ddr4_cw.rc0f.latency_adder_nladd_to_all_dram_cmd;
    else
        ddr4_rcd_latency_adder_nladd_to_all_dram_cmd = 0;
    if (IS_DDR4) {
        if (hdlr->memCtrlr_m.ddr4_mr[p].mr5.read_dbi == 1) {
            PRE_CFG.dfi_t_rddata_en[p][dch] = dfi_t_rddata_en_int + timing->ddr4_tpl_tck +
                (timing->ddr4_tcl_rdbi_tck - PRE_CFG.cl[p]) + (SPD.tAL_RDBI - SPD.tAL)
                + trddata_en_pipe + ddr4_rcd_latency_adder_nladd_to_all_dram_cmd;
            PRE_CFG.dfi_tphy_wrlat[p][dch] = (SPD.tAL_RDBI + PRE_CFG.cwl_x[p] + timing->ddr4_tpl_tck - DFI_WL_SUB)
                + tphy_wrlat_pipe + ddr4_rcd_latency_adder_nladd_to_all_dram_cmd;
        } else {
            PRE_CFG.dfi_t_rddata_en[p][dch] = dfi_t_rddata_en_int + timing->ddr4_tpl_tck
                + trddata_en_pipe + ddr4_rcd_latency_adder_nladd_to_all_dram_cmd;
            PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + timing->ddr4_tpl_tck
                + tphy_wrlat_pipe + ddr4_rcd_latency_adder_nladd_to_all_dram_cmd;
        }
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
	if (IS_DDR5) {
        // When DDRCTL_EXT_SBECC_AND_CRC is defined, dfi_tphy_wrlat is not calculated here. Please add code to cinit_cal_delay_for_ras_model.
		ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
		if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
		  if (IS_RDIMM || IS_LRDIMM) {

			PRE_CFG.dfi_t_rddata_en[p][dch] = dfi_t_rddata_en_int + ac_in_pipe - dx_in_pipe + trddata_en_pipe + hdlr->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd;
          // When DDRCTL_EXT_SBECC_AND_CRC is defined, dfi_tphy_wrlat is not calculated here. Please add code to cinit_cal_delay_for_ras_model of dwc_ddrctl_cinit_pre_cfg.c.
		  #ifndef DDRCTL_EXT_SBECC_AND_CRC
			PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + ac_in_pipe - dx_in_pipe + tphy_wrlat_pipe + hdlr->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd;
          #endif
		  } else {
			PRE_CFG.dfi_t_rddata_en[p][dch] = dfi_t_rddata_en_int + ac_in_pipe - dx_in_pipe + trddata_en_pipe;
          // When DDRCTL_EXT_SBECC_AND_CRC is defined, dfi_tphy_wrlat is not calculated here. Please add code to cinit_cal_delay_for_ras_model of dwc_ddrctl_cinit_pre_cfg.c.
		  #ifndef DDRCTL_EXT_SBECC_AND_CRC
			PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + ac_in_pipe - dx_in_pipe + tphy_wrlat_pipe;
          #endif
		  }
         #ifndef DWC_PHYINIT_RID_GE202211
          // adjust read latency of crc is enabled
          if(QDYN.rd_crc_enable && tck_ps < 312)
              PRE_CFG.dfi_t_rddata_en[p][dch] -= 2;
         #endif
         #ifdef DWC_PHYINIT_RID_GE202211
          if(QDYN.rd_crc_enable)
            PRE_CFG.dfi_t_rddata_en[p][dch] +=timing->ddr5_read_crc_latency_adder;
         #endif
		} else {
		 if (IS_RDIMM || IS_LRDIMM) {

			PRE_CFG.dfi_t_rddata_en[p][dch] = dfi_t_rddata_en_int + trddata_en_pipe + hdlr->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd;
         // When DDRCTL_EXT_SBECC_AND_CRC is defined, dfi_tphy_wrlat is not calculated here. Please add code to cinit_cal_delay_for_ras_model.
		 #ifndef DDRCTL_EXT_SBECC_AND_CRC
			PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + tphy_wrlat_pipe + hdlr->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd;
		 #endif
		 } else {
			PRE_CFG.dfi_t_rddata_en[p][dch] = dfi_t_rddata_en_int + trddata_en_pipe;
         // When DDRCTL_EXT_SBECC_AND_CRC is defined, dfi_tphy_wrlat is not calculated here. Please add code to cinit_cal_delay_for_ras_model.
		 #ifndef DDRCTL_EXT_SBECC_AND_CRC
			PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + tphy_wrlat_pipe;
		 #endif
		 }
		}
if (hdlr->ddrPhyType_m != DWC_DDR5_PHY) {
#ifndef DWC_PHYINIT_RID_GE202102
        // adjust read latency of crc is enabled
        if(QDYN.rd_crc_enable)
            PRE_CFG.dfi_t_rddata_en[p][dch] +=timing->ddr5_read_crc_latency_adder;
#else
  #ifndef DWC_PHYINIT_RID_GE202201
        // In Skip train mode currently the PHYINIT compensates for read crc latency adder,
        // firmware(only full training) does not (which aligns with PUB databook
      if(QDYN.rd_crc_enable) {
        if (hdlr->phy_training == 0)
            PRE_CFG.dfi_t_rddata_en[p][dch] +=timing->ddr5_read_crc_latency_adder;
      }
  #else
       // adjust read latency of crc is enabled
        if(QDYN.rd_crc_enable)
            PRE_CFG.dfi_t_rddata_en[p][dch] +=timing->ddr5_read_crc_latency_adder;
  #endif
#endif // DWC_PHYINIT_RID_GE202102
    }
   }
#endif /* CINIT_DDR5 */

	  /** @brief Table 5-12 of phy databook 1.00a, unit : DFI clock */
	  if (IS_DDR4 && (IS_RDIMM || IS_LRDIMM)) {
		    // use -1 for RDIMM as otherwise tCKSRE errors by one DRAM clock
		    PRE_CFG.dfi_t_dram_clk_disable[p][dch] = QDYN.dfi_t_ctrl_delay[p][dch] - 1;
	  } else {
		    PRE_CFG.dfi_t_dram_clk_disable[p][dch] = QDYN.dfi_t_ctrl_delay[p][dch];
  	}
	  PRE_CFG.dfi_t_dram_clk_enable[p][dch] = QDYN.dfi_t_ctrl_delay[p][dch];

    // Table 5-8 DFI Low Power control timing parameters
    hdlr->phy_timing_params.dfi_tlp_resp = 2 * hdlr->phy_timing_params.pipe_dfi_misc + 1; // 1:2 mode
    hdlr->phy_timing_params.dfi_tlp_data_wakeup = 2 * hdlr->phy_timing_params.pipe_dfi_misc + 2; // 1:2 mode
    hdlr->phy_timing_params.dfi_t_2n_mode_delay = 4 + hdlr->phy_timing_params.pipe_dfi_misc; // 1:2 mode
#ifdef CINIT_DDR5
    if (IS_DDR5 && hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
      hdlr->phy_timing_params.dfi_tlp_resp = 2 * hdlr->phy_timing_params.pipe_dfi_misc + 2; // 1:2 mode
      hdlr->phy_timing_params.dfi_t_2n_mode_delay = 4 + ac_in_pipe; // 1:2 mode
    }
#endif
    if (ratio==2)
        hdlr->phy_timing_params.dfi_t_ctrlup_min = 2 + 2 * hdlr->phy_timing_params.pipe_dfi_misc;
    else
        hdlr->phy_timing_params.dfi_t_ctrlup_min = CEIL((3 + 2 * hdlr->phy_timing_params.pipe_dfi_misc),2); // round up

	  if (IS_DDR5 && hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
        hdlr->phy_timing_params.dfi_t_ctrlup_min = 2 + 2 * hdlr->phy_timing_params.pipe_dfi_misc;
        }
    uint32_t ext = dwc_ddrctl_cinit_cal_ddr54_ext(hdlr,p);

    if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
        hdlr->phy_timing_params.dfi_t_ctrlup_max = 25 + 2 * hdlr->phy_timing_params.pipe_dfi_misc + ext;
    } else {
        if (ratio == 2) {
            hdlr->phy_timing_params.dfi_t_ctrlup_max = 19 + 2 * hdlr->phy_timing_params.pipe_dfi_misc + ext;
        } else {
            hdlr->phy_timing_params.dfi_t_ctrlup_max = CEIL((20 + 2 * hdlr->phy_timing_params.pipe_dfi_misc + ext),2) + 1;// round up
        }
    }

    if (hdlr->ddrPhyType_m != DWC_DDR5_PHY) {
        if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_1_4) {
            // 1:4 mode
            hdlr->phy_timing_params.dfi_tlp_resp = ((2 * hdlr->phy_timing_params.pipe_dfi_misc + 2) >> 1) + 1;
            hdlr->phy_timing_params.dfi_t_2n_mode_delay = hdlr->phy_timing_params.dfi_t_2n_mode_delay >> 1;
            hdlr->phy_timing_params.dfi_tlp_data_wakeup = (hdlr->phy_timing_params.dfi_tlp_data_wakeup >> 1)+ 1;
        }
    }
    hdlr->phy_timing_params.dfi_tphy_wrdata = (IS_DDR5) ? 6 : 2;
  #ifndef DDRCTL_EXT_SBECC_AND_CRC
    PRE_CFG.dfi_tphy_wrdata[p][dch] = hdlr->phy_timing_params.dfi_tphy_wrdata;
  #endif

#endif /* DDRCTL_DDR */
}

void dwc_ddrctl_cinit_ddr54_prgm_REGB_FREQ_DFITMG2(uint32_t freq, uint32_t ch)
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

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG2, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}

#ifdef DDRCTL_DDR
void dwc_ddrctl_cinit_ddr54_prgm_REGB_FREQ_DFITMG7(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG7_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg7,
        &REGB_FREQ_CH1(freq).dfitmg7
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.dfi_t_init_start[freq][ch] = PRE_CFG.dfi_t_init_start[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_t_init_start, ch, freq);

    QDYN.dfi_t_init_complete[freq][ch] = PRE_CFG.dfi_t_init_complete[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_t_init_complete, ch, freq);

    QDYN.dfi_t_2n_mode_delay[freq][ch] = hdlr->phy_timing_params.dfi_t_2n_mode_delay;
    QDYN_CFG_MATRIX(ptr, dfi_t_2n_mode_delay, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
    dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG7, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_DDR */


/** @brief method to implement Table 5-1 of phy databook, DFI clock (unit) for either D54 PHY*/
void dwc_ddrctl_cinit_ddr54_dfi_control_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch)
{
#ifdef DDRCTL_DDR
    SNPS_TRACE("Entering");
    // DDR54 PHY
    //1:2((ARdPtrinitVal[3:0]/2)+(MISC*2)+3+1+AT)/2, ARdPtrinitVal[3:0]=3UI, AT=0 for skip_train test
    //1:4((ARdPtrinitVal[3:0]/2)+(MISC*2)+3+3+AT)/4
    // DDR5 PHY
    //1:2((PclkPtrinitVal[4:0] + 1/2) +3.5+1+AT)/2, ARdPtrinitVal[3:0]=3UI, AT=0 for skip_train test
    //1:4((PclkPtrinitVal[4:0] + 1/2) +3+5+AT)/4
    if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
        if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_1_4) // 1:4 mode
            QDYN.dfi_t_ctrl_delay[p][ch] = 3;
        else
            QDYN.dfi_t_ctrl_delay[p][ch] = 4;
    } else {
        if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_1_4) // 1:4 mode
            QDYN.dfi_t_ctrl_delay[p][ch] = 2 + 2 * DIV_4(hdlr->phy_timing_params.pipe_dfi_misc);
        else
            QDYN.dfi_t_ctrl_delay[p][ch] = 3 + 2 * DIV_2(hdlr->phy_timing_params.pipe_dfi_misc);
    }
#ifdef DDRCTL_EXT_SBECC_AND_CRC
    SNPS_LOG("original QDYN.dfi_t_ctrl_delay[p][ch]= %u", QDYN.dfi_t_ctrl_delay[p][ch]);
    QDYN.dfi_t_ctrl_delay[p][ch] = QDYN.dfi_t_ctrl_delay[p][ch] + hdlr->dfi_ras_model_cmd_delay;
#endif
    SNPS_TRACE("Leaving");

#endif // DDRCTL_DDR
}

void cinit_cal_ddr54_pre_cfg_timing_1st_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
#ifdef DDRCTL_DDR
    uint32_t tck_ps = SPD.tck_ps[p];
#ifdef CINIT_DDR5
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    uint32_t ratio;

    ratio = ddrctl_sw_get_ratio_factor(hdlr, p);

    if (IS_DDR5) {
        PRE_CFG.dfi_t_init_start[p][ch] = 1024 / ratio;
        // update dfi_t_init_complete programming based on new equation in DDR5/4 phy PUB 4.10a,
        PRE_CFG.dfi_t_init_complete[p][ch] = (CEIL(3000000 + timing->ddr5_rcd_tstab01_max_ps, tck_ps) + ratio - 1) / ratio + 6384 / ratio;
    }
#endif /* CINIT_DDR5 */

#ifdef CINIT_DDR4
    if (IS_DDR4) {
        PRE_CFG.dfi_t_init_start[p][ch] = 512;
        // update dfi_t_init_complete programming based on new equation in DDR5/4 phy PUB 4.10a,
        PRE_CFG.dfi_t_init_complete[p][ch] = DIV_2(cinit_ps_to_tck(3000000, tck_ps) + 1) + 3192;
        }
#endif /* CINIT_DDR4 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_CAPAR_RETRY
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        // tphy_rdlat(max) : large enough to handle worst case value observed from PHY in DDR5
        #ifndef DDRCTL_DDR5CTL_HIGHSPEED
          if (IS_LRDIMM) {
            PRE_CFG.dfi_t_phy_rdlat[p][ch] = 60;
          } else {
            PRE_CFG.dfi_t_phy_rdlat[p][ch] = 56;
          }
        #else
          //When speedgrade upto 8000, rdlat need to be updated to 64.
          PRE_CFG.dfi_t_phy_rdlat[p][ch] = 64;
        #endif /*DDRCTL_DDR5CTL_HIGHSPEED*/
        if (hdlr->ddrPhyType_m == DWC_DDR5_PHY){
          PRE_CFG.dfi_t_phy_rdlat[p][ch] = 84;
        }
#ifdef DDRCTL_EXT_SBECC_AND_CRC  
        PRE_CFG.dfi_t_phy_rdlat[p][ch] = PRE_CFG.dfi_t_phy_rdlat[p][ch] + hdlr->rd_path_delay * ratio;
#endif
        }
#endif /* CINIT_DDR5 */
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        // tphy_rdlat(max) : large enough to handle worst case value observed from PHY in DDR4
        PRE_CFG.dfi_t_phy_rdlat[p][ch] = 48;
        }
#endif /* CINIT_DDR4 */
#endif /* DDRCTL_CAPAR_RETRY */

}

