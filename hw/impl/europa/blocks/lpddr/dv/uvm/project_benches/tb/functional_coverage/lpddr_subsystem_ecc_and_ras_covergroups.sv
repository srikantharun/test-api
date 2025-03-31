//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_ecc_and_ras_covergroups.sv
//---------------------------------------------------------------------------
//Description :
//---------------------------------------------------------------------------
`ifndef LPDDR_SUBSYSTEM_ECC_AND_RAS_COVERGROUPS
`define LPDDR_SUBSYSTEM_ECC_AND_RAS_COVERGROUPS
  
//-----------------------------------------------------------------------------
// Covergroup Name : cg_link_ecc
// Description     :  
// Arguments       : 1).
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 7.1 from TP
// TODO : did not gound hpr_num signal
//---------------------------------------------------------------------------------------------
covergroup cg_link_ecc with function sample (bit [31:0] linkeccctl0,
                                             bit [31:0] linkeccindex,
																						 bit [31:0] linkeccerrcnt0,
																						 bit [31:0] linkeccpoisonctl0,
																						 bit rd_linkecc_corr_err_intr,
																						 bit rd_linkecc_uncorr_err_intr,
																						 bit [1:0] rd_linkecc_corr_err_intr_fault,
																						 bit [1:0] rd_linkecc_uncorr_err_intr_fault);
  option.per_instance = 1;
	type_option.merge_instances = 0;
	cp_wr_link_ecc_enable : coverpoint linkeccctl0[0] {
		bins cb_linkeccctl0_wr_link_ecc_enable [] = {1'b0, 1'b1};
	}
	
	cp_rd_link_ecc_enable : coverpoint linkeccctl0[1] {
		bins cb_linkeccctl0_rd_link_ecc_enable [] = {1'b0, 1'b1};
	}

	cp_rd_lonk_ecc_err_byte_sel : coverpoint linkeccindex[2:0] {
		bins cb_linkeccindex_rd_lonk_ecc_err_byte_sel [] = {[3'd0:3'd3]};
	}

	cp_rd_lonk_ecc_err_rank_sel : coverpoint linkeccindex[5:4] {
		bins cb_linkeccindex_rd_lonk_ecc_err_rank_sel [] = {2'b00, 2'b01};
	}
	
	cp_rd_link_ecc_err_syndrome : coverpoint linkeccerrcnt0[8:0] {
		bins cb_linkeccerrcnt0_rd_link_ecc_err_syndrome [5] = {[9'd0:9'd511]};
	}
	// TODO : rd_lonk_ecc_corr_cnt [23:16] & rd_lonk_ecc_uncorr_cnt [31:24]
	// TODO : linkeccpoisonctl0
  
	cp_rd_linkecc_corr_err_intr : coverpoint rd_linkecc_corr_err_intr {
    bins cb_rd_linkecc_corr_err_intr [] = {1'b0, 1'b1};
	}

	cp_rd_linkecc_uncorr_err_intr : coverpoint rd_linkecc_uncorr_err_intr {
    bins cb_rd_linkecc_uncorr_err_intr [] = {1'b0, 1'b1};
	}

	cp_rd_linkecc_corr_err_intr_fault : coverpoint rd_linkecc_corr_err_intr {
    bins cb_rd_linkecc_corr_err_intr_fault [] = {2'b01, 2'b10};
	}

	cp_rd_linkecc_uncorr_err_intr_fault : coverpoint rd_linkecc_uncorr_err_intr {
    bins cb_rd_linkecc_uncorr_err_intr_fault [] = {2'b01, 2'b10};
	}
endgroup : cg_link_ecc

//-----------------------------------------------------------------------------
// Covergroup Name : cg_post_package_repair_test
// Description     :  
// Arguments       : mrctrl0_ppr_en, mrctrl0_mr_wr, mrctrl0_ppr_pgmpst_en,
//                   mrstat_ppr_done
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 7.2 from TP
//-----------------------------------------------------------------------------
covergroup cg_post_package_repair_test with function sample (bit mrctrl0_ppr_en,
                                                             bit mrctrl0_mr_wr,
																												     bit mrctrl0_ppr_pgmpst_en,
																												     bit mrstat_ppr_done);       
  option.per_instance = 1;
	type_option.merge_instances = 0;

  cp_mrctrl0_ppr_en : coverpoint mrctrl0_ppr_en {
		bins cb_mrctrl0_ppr_en [] = {1'b0, 1'b1};
	}

	cp_mrctrl0_mr_wr : coverpoint mrctrl0_mr_wr {
	  bins cb_mrctrl0_mr_wr [] = {1'b0, 1'b1};
	}

	cp_mrctrl0_ppr_pgmpst_en : coverpoint mrctrl0_ppr_pgmpst_en {
	  bins cb_mrctrl0_ppr_pgmpst_en [] = {1'b0, 1'b1};
	}

	cp_mrctrl0_ppr_done : coverpoint mrstat_ppr_done {
	  bins cb_mrctrl0_ppr_done [] = {1'b0, 1'b1};
	}

  //cp_cross_pageclose_X_pageclose_timer : cross cp_pageclose, cp_pageclose_timer;
	cp_cross_mrctrl0_ppr_en_X_mrctrl0_mr_wr : cross cp_mrctrl0_ppr_en, cp_mrctrl0_mr_wr;

	cp_cross_mrctrl0_mr_wr_X_mrctrl0_ppr_pgmpst_en : cross cp_mrctrl0_mr_wr, cp_mrctrl0_ppr_pgmpst_en;
endgroup : cg_post_package_repair_test

//-----------------------------------------------------------------------------
// Covergroup Name : cg_inline_ecc
// Description     :  
// Arguments       : 1).
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 7.3 from TP
// TODO : did not gound hpr_num signal
//-----------------------------------------------------------------------------
covergroup cg_inline_ecc with function sample ( bit [31:0] ecccfg0,
                                                bit [1:0] ecccfg0_ecc_region_map_granu,
																								bit [7:0] ecccfg0_ecc_region_map,
																								bit ecccfg0_ecc_region_map_en,
																								bit ecccfg0_ecc_region_map_other,
																								bit ecccfg1_ecc_region_parity_lock,
																								bit ecccfg0_ecc_ap_en,
																								bit ecccfg1_ecc_region_waste_lock,
																								bit ecccfg1_med_ecc_en,
																								bit ecccfg1_ecc_ap_mode,
                                                bit [31:0] ecccfg1, 
																								bit [2:0] dbg_dfi_ie_cmd_type,    //TODO :- how we can take this siganl, path ?
																								bit ecc_ap_err_intr,
																								bit ecc_corrected_err_intr,
																								bit ecc_uncorrected_err_intr,
																								bit ecc_ap_err_intr_fault, //01, 10
																								bit ecc_corrected_err_intr_fault, 
																								bit ecc_uncorrected_err_intr_fault																							
																							);
  option.per_instance = 1;
	type_option.merge_instances = 0;
  cp_ecccfg0_ecc_region_map_granu : coverpoint ecccfg0_ecc_region_map_granu {
		bins cb_ecc_region_map_granu [] = {[2'd0:2'd3]};
	}
	
	cp_ecccfg0_ecc_region_map : coverpoint ecccfg0_ecc_region_map {
		bins cb_ecc_region_map [] = {[7'd0:7'd50],[7'd51:7'd100],[7'd101:7'd127]};  //TODO :- need to cover cores wih grunu
	}

	cp_ecccfg0_ecc_region_map_en : coverpoint ecccfg0_ecc_region_map_en {
		bins cb_ecc_region_map_en [] = {1'b0, 1'b1};
	}

//	cp_ecccfg0_ecc_region_map_en : coverpoint ecccfg0[7] {
//		bins cb_ecc_region_map_en [] = {1'b0, 1'b1};
//	}

	cp_ecccfg0_ecc_region_map_other : coverpoint ecccfg0_ecc_region_map_other {
		bins cb_ecc_region_map_other [] = {1'b0, 1'b1};
	}

	cp_ecccfg1_ecc_region_parity_lock : coverpoint ecccfg1_ecc_region_parity_lock {
		bins cb_ecc_region_parity_lock [] = {1'b0, 1'b1};
	}

  cp_ecccfg1_ecc_region_waste_lock : coverpoint ecccfg1_ecc_region_waste_lock {
		bins cb_ecc_region_waste_lock [] = {1'b0, 1'b1};
	}
	
	cp_ecccfg0_ecc_ap_en : coverpoint ecccfg0_ecc_ap_en {
		bins cb_ecc_ap_en [] = {1'b0, 1'b1};
	}
	
	cp_ecccfg1_med_ecc_en : coverpoint ecccfg1_med_ecc_en {
		bins cb_med_ecc_en [] = {1'b0, 1'b1};
	}
	
	cp_ecccfg1_ecc_ap_mode : coverpoint ecccfg1_ecc_ap_mode {
		bins cb_ecc_ap_mode [] = {1'b0, 1'b1};
	}

	//	cp_dbg_dfi_ie_cmd_type : coverpoint dbg_dfi_ie_cmd_type {
	//		bins cb_rd_command [4] = {3'b000, 3'b001, 3'b010, 3'b111} iff (command == RD/RDA);  //TODO need to find cmd signal & RD/RDA value also
	//		bins cb_wr_command [4] = {3'b000, 3'b001, 3'b010, 3'b111} iff (command == WR/WRA);
	//	}

	cp_ecc_corrected_err_intr : coverpoint ecc_corrected_err_intr {
    bins cb_ecc_corrected_err_intr [] = {1'b0, 1'b1};
	}
	
	cp_ecc_uncorrected_err_intr : coverpoint ecc_uncorrected_err_intr {
    bins cb_ecc_uncorrected_err_intr [] = {1'b0, 1'b1};
	}

	cp_ecc_ap_err_intr_fault : coverpoint ecc_ap_err_intr_fault {
    bins cb_ecc_ap_err_intr_fault [] = {2'b01, 2'b10};
	}
	
	cp_ecc_corrected_err_intr_fault : coverpoint ecc_corrected_err_intr_fault {
    bins cb_ecc_corrected_err_intr_fault [] = {1'b0, 1'b1};
	}
	
	cp_ecc_uncorrected_err_intr_fault : coverpoint ecc_uncorrected_err_intr_fault {
    bins cb_ecc_uncorrected_err_intr_fault [] = {1'b0, 1'b1};
	}
endgroup : cg_inline_ecc

//-----------------------------------------------------------------------------
// Covergroup Name : cg_scrubber_status
// Description     :  
// Arguments       : sbr_resetn, sbrctl_scrub_interval, pwrtmg_powerdown_to_x32,
//                   pwrtmg_selfref_to_x32, sbrctl_scrub_en, sbrstart0_sbr_address_start_mask_0,
//		               sbrstart1_sbr_address_start_mask_1, sbrrange0_sbr_address_range_mask_0,
//									 sbrrange0_sbr_address_range_mask_1, sbrstat_scrub_busy,
//									 sbrstat_scrub_done, sbrctl_scrub_during_lowpower,
//									 pwrctl_powerdown_en, pwrctl_selfref_en, pwrctl_selfref_sw 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 7.4 from TP
//-----------------------------------------------------------------------------
covergroup cg_scrubber_status with function sample (bit sbr_resetn,
																										bit [12:0] sbrctl_scrub_interval,
																										bit [6:0] pwrtmg_powerdown_to_x32,
																										bit [9:0] pwrtmg_selfref_to_x32,
                                                    bit sbrctl_scrub_en,
																										bit [31:0] sbrstart0_sbr_address_start_mask_0,
																										bit [7:0] sbrstart1_sbr_address_start_mask_1,
																										bit [31:0] sbrrange0_sbr_address_range_mask_0,
																										bit [7:0] sbrrange0_sbr_address_range_mask_1,
																										bit sbrstat_scrub_busy,
																										bit sbrstat_scrub_done,
																										bit sbrctl_scrub_during_lowpower,
																										bit pwrctl_powerdown_en,
																										bit pwrctl_selfref_en,
																										bit pwrctl_selfref_sw);
  option.per_instance = 1;
	type_option.merge_instances = 0;
  //TODO:Add coverpoint for below:
  //Cover default values of SBR logic on sbr_resetn=0

  cp_sbrstat_scrub_interval_1 : coverpoint sbrctl_scrub_interval {
	  bins cb_sbrstat_scrub_interval_1 = {13'h0};
	}

  cp_sbrstat_scrub_interval_2 : coverpoint (sbrctl_scrub_interval==pwrtmg_powerdown_to_x32) {
	  bins cb_sbrstat_scrub_interval_2 = {1'b1};
	}

  cp_sbrstat_scrub_interval_3 : coverpoint (sbrctl_scrub_interval==pwrtmg_selfref_to_x32) {
	  bins cb_sbrstat_scrub_interval_3 = {1'b1};
	}

  cp_sbrstat_scrub_interval_4 : coverpoint ((sbrctl_scrub_interval!=pwrtmg_selfref_to_x32) && (sbrctl_scrub_interval!=pwrtmg_powerdown_to_x32) && (sbrctl_scrub_interval!=0)) {
	  bins cb_sbrstat_scrub_interval_4 = {1'b1};
	}

  cp_sbrctl_scrub_en : coverpoint sbrctl_scrub_en {
	  bins cb_sbrctl_scrub_en []= {1'b0, 1'b1};
	}

	cp_sbrstart0_sbr_address_start_mask_0 : coverpoint sbrstart0_sbr_address_start_mask_0 {
	  bins cb_sbrstart0_sbr_address_start_mask_0 [5] = {[32'h0:32'hFFFFFFFF]};
	}

	cp_sbrstart1_sbr_address_start_mask_1 : coverpoint sbrstart1_sbr_address_start_mask_1 {
	  bins cb_sbrstart1_sbr_address_start_mask_1 [5] = {[8'd0:8'd255]};
	}

	cp_sbrstart0_sbr_address_range_mask_0 : coverpoint sbrrange0_sbr_address_range_mask_0 {
	  bins cb_sbrstart0_sbr_address_range_mask_0 [5] = {[32'h0:32'hFFFFFFFF]};
	}

	cp_sbrstart0_sbr_address_range_mask_1 : coverpoint sbrrange0_sbr_address_range_mask_1 {
	  bins cb_sbrstart0_sbr_address_range_mask_1 [5] = {[8'd0:8'd255]};
	}

	cp_sbrstat_scrub_interval_busy_done : coverpoint {(sbrctl_scrub_interval!=0), sbrstat_scrub_busy, sbrstat_scrub_done} {
	  bins cb_sbrstat_scrub_interval_busy_done = {3'b110};
	}

	cp_sbrstat_scrub_busy : coverpoint {sbrctl_scrub_interval, sbrstat_scrub_busy, sbrstat_scrub_done} {
	  bins cb_sbrstat_scrub_busy_1 = {3'b011};
	  bins cb_sbrstat_scrub_busy_2 = {3'b001};
	}

  cp_sbrctl_scrub_during_lowpower : coverpoint sbrctl_scrub_during_lowpower iff((pwrctl_powerdown_en == 1) && (pwrctl_selfref_en ==1) && (pwrctl_selfref_sw ==1)){
	  bins cb_sbrctl_scrub_during_lowpower [] = {1'b1, 1'b0};	
	}
endgroup : cg_scrubber_status
`endif // LPDDR_SUBSYSTEM_ECC_AND_RAS_COVERGROUPS
