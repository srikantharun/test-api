//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_initialization_covergroups.sv 
//---------------------------------------------------------------------------
//Description :
//---------------------------------------------------------------------------

`ifndef LPDDR5_SUBSYSTEM_LOW_POWER_AND_POWER_SAVING_FEATURES_COVERGROUPS
`define LPDDR5_SUBSYSTEM_LOW_POWER_AND_POWER_SAVING_FEATURES_COVERGROUPS

// Section Number : 6.1
// Section Name   : Pre-charge Power down Test

//-----------------------------------------------------------------------------
// Covergroup  : cg_pre_charge_power_down
// Arguments   : 
// Description : This covergroup is for test <Pre-Charge Power Down Test>.
//TODO : To change the time period as per speed bins for axi idle coverpoint
//-----------------------------------------------------------------------------
covergroup cg_pre_charge_power_down with function sample(bit PWRCTL_powerdown_en_bit_x_to_4, // TODO : need to confirm width of this register
                                                         bit DFILPCFG0_dfi_lp_en_pd_bit_0,
																								         bit [6:0] PWRTMG_powerdown_to_x32_bit_6_to_0,
																								         bit [4:0] DFILPTMG0_dfi_lp_wakeup_pd_bit_4_to_0,
																								         time axi_idle_time
																								         //lpddr_op_mode_e op_mode
																								         );

  option.per_instance = 1;
  type_option.merge_instances = 0;

	cp_PWRCTL_powerdonw_en_bit_x_to_4 : coverpoint PWRCTL_powerdown_en_bit_x_to_4 {
	  option.comment = "This coverpoint covers both the values of field powerdown_en of Register PWRCTL";
    bins cb_logic_0 = {1'b0}; // For LPDDR5 only bit[4] is used : bit[4] - rank 0 powerdown_en
		bins cb_logic_1 = {1'b1}; // For LPDDR5 only bit[4] is used : bit[4] - rank 0 powerdown_en
	}

	cp_DFILPCFG0_dfi_lp_en_pd_bit_0 : coverpoint DFILPCFG0_dfi_lp_en_pd_bit_0 {
	  option.comment = "This coverpoint covers both the values of field dfi_lp_en_pd of Register DFIPCFG0";   
    bins cb_logic_0 = {1'b0}; 
		bins cb_logic_1 = {1'b1}; // Controller will put PHY in Low Power mode through DFI Low Power Interface.
	}

	cp_PWRTMG_powerdown_to_x32_bit_6_to_0 : coverpoint PWRTMG_powerdown_to_x32_bit_6_to_0 {
	  option.comment = "This coverpoint covers different combinations of powerdown_to_x32 of Register PWRTMG";
    bins cb_range_1 = {[7'd0:7'd31]};   // with interval of 2^7/4 
		bins cb_range_2 = {[7'd32:7'd64]};  // with interval of 2^7/4 
		bins cb_range_3 = {[7'd65:7'd97]};  // with interval of 2^7/4 
		bins cb_range_4 = {[7'd98:7'd127]}; // with interval of 2^7/4
	}

	cp_DFILPTMG0_dfi_lp_wakeup_pd_bit_4_to_0 : coverpoint DFILPTMG0_dfi_lp_wakeup_pd_bit_4_to_0 {
	  option.comment = "This coverpoint covers different combinations of dfi_lp_wakeup_pd of Register DFILPTMG0";
	  bins cb_value[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13}; 
	}

	cp_axi_idle_time : coverpoint {axi_idle_time < (PWRTMG_powerdown_to_x32_bit_6_to_0 * 32 *1.25),axi_idle_time > (PWRTMG_powerdown_to_x32_bit_6_to_0 * 32 *1.25)}{
	    option.comment = "This coverpoint covers that idle period without any axi tx is less or greater than the power down timing";
	    bins cb_is_less  = {2'b10};
      bins cb_is_great = {2'b01};
	}
  
	// TODO : 6.1.5 
endgroup : cg_pre_charge_power_down

// Section Number : 6.2
// Section Name   : Self Refresh Test

//-----------------------------------------------------------------------------
// Covergroup Name : cg_self_refresh
// Arguments       : 
// Description     : This covergroup is for test <Self Refresh Test>
//-----------------------------------------------------------------------------
//TODO Nikhil : To change the time period as per speed bins for axi idle coverpoint
covergroup cg_self_refresh with function sample(bit PWRCTL_selfref_en_bit_x, // TODO : Need to confirm width
                                                bit PWRCTL_selfref_sw_bit_11,
																								bit PWRCTL_stay_in_selfref_bit_15,
																								bit DFILPCFG0_dfi_lp_en_sr_bit_4,
																								bit [9:0] PWRTMG_selfref_to_x32_bit_25_to_16,
																								bit [4:0] DFILPCFG0_dfi_lp_en_sr_bit_12_to_8,
																								bit HWLPCTL_hw_lp_en_bit_0,
																								time axi_idle_time
																								//TODO Nikhil : selfref_type_e selfref_type,
																								//TODO Nikhil : selfref_state_e selfref_state
																				        //TODO Nikhil : cysyreq/csysack/cative_in_ddrc
																				       );
	
  option.per_instance = 1;
  type_option.merge_instances = 0;
	
	PWRCTL_selfref_en_bit_x : coverpoint PWRCTL_selfref_en_bit_x {
	  option.comment = "This coverpoint covers both the value of field selfref_en  of Register PWRCTL";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

	PWRCTL_selfref_sw_bit_11 : coverpoint PWRCTL_selfref_sw_bit_11 {
	  option.comment = "This coverpoint covers both the value of field selfref_sw of Register PWRCTL";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

	cp_PWRCTL_stay_in_selfref_bit_ : coverpoint PWRCTL_stay_in_selfref_bit_15 {
	  option.comment = "This coverpoint covers both the value of field stay_in_selfref of Register PWRCTL";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

	cp_DFILPCFG0_dfi_lp_en_sr_bit_4 : coverpoint DFILPCFG0_dfi_lp_en_sr_bit_4 {
	  option.comment = "This coverpoint covers both the value of field dfi_lp_en_sr of Register DFILPCFG0";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

	cp_PWRTMG_selfref_to_x32_bit_ : coverpoint PWRTMG_selfref_to_x32_bit_25_to_16 {
	  option.comment = "This coverpoint covers different values of filed selfref_to_x32 of Register PWRTMG";
    bins cb_range_1 = {[10'd1:10'd255]}; 
    bins cb_range_2 = {[10'd256:10'd511]}; 
    bins cb_range_3 = {[10'd512:10'd767]}; 
    bins cb_range_4 = {[10'd768:10'd1023]}; 
	}

	cp_DFILPCFG0_dfi_lp_en_sr_bit_ : coverpoint DFILPCFG0_dfi_lp_en_sr_bit_12_to_8 {
	  option.comment = "This coverpoint covers different values of field dfi_lp_en_sr of Register DFILPCFG0";
	  bins cb_value[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13}; 
	}

	cp_HWLPCTL_hw_lp_en_bit_0 :  coverpoint HWLPCTL_hw_lp_en_bit_0 {
		bins cb_logic_1 = {1'b1};
	}
	
	cp_axi_idle_time : coverpoint {axi_idle_time < (PWRTMG_selfref_to_x32_bit_25_to_16 * 32 *1.25),axi_idle_time > (PWRTMG_selfref_to_x32_bit_25_to_16 * 32 *1.25)}{
	    option.comment = "This coverpoint covers that idle period without any axi tx is less or greater than the self ref timing";
	    bins cb_is_less  = {2'b10};
      bins cb_is_great = {2'b01};
	}

	//TODO : Nikhil
 /* cp_selfref_type : coverpoint selfref_type {
		  bins cb_not_selfref = {NOT_SELFREF};
		//	bins cb_automatic   = {AUTOMATIC_SELFREF};
			bins cb_sw          = {SELFREF_BY_SW};
		//	bins cb_PHY_MSTR    = {PHY_MSTR};
	}

	cp_selfref_type : coverpoint selfref_state{
	    bins cb_not_selfref = {NOT_IN_SELFREF};
      bins cb_power_down  = {SELFREF_POWERDOWN};
			bins cb_deep_sleep  = {DEEP_SLEEP};
	}  */

endgroup : cg_self_refresh


// Section Number : 6.3
// Section Name   : Deep Sleep Mode Test

//-----------------------------------------------------------------------------
// Covergroup Name : cg_deep_sleep_mode
// Arguments       : 
// Description     : This covergroup is for test <Deep Sleep Mode Test>.
//-----------------------------------------------------------------------------
covergroup cg_deep_sleep_mode with function sample(bit PWRCTL_dsm_en_bit_18,
                                                   bit DFILPCFG0_dfi_lp_en_dsm_bit_8,
																									 bit [4:0] DFILPTMG0_dfi_lp_wakeup_sr_bit_12_to_8,
																									 bit PWRCTL_selfref_sw_bit_11,
																									 bit PWRCTL_selfref_en_bit_x, // TODO : Need to confirm width 
																									 bit HWLPCTL_hw_lp_en_bit_0,
																									 bit DFIPHYMSTR_dfi_phymstr_en_bit_0,
																									 //bit DFIPHYMSTR_dfi_error_bit_,// TODO : Need to confirm dif_error is part of register or it is input pin.Nikhil : Maybe we need to remove this
																									 bit [2:0] STAT_selfref_state_bit_14_to_12,
																									 bit [4:0] DFILPTMG0_dfi_lp_wakeup_dsm_bit_20_to_16,
																									 bit [4:0] DFILPTMG0_dfi_lp_wakeup_pd_bit_4_to_0,
																									 bit [4:0] DFILPTMG1_dfi_lp_wakeup_data_bit_4_to_0,
																									 bit [4:0] DFITMG1_dfi_tlp_resp_bit_12_to_8
                                                    );
  option.per_instance = 1;
  type_option.merge_instances = 0;

	cp_PWRCTL_dsm_en_bit_ : coverpoint PWRCTL_dsm_en_bit_18 {
	  option.comment = "This coverpoint covers both the value of field dsm_en of Register PWRCTL";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

  cp_DFILPCFG0_dfi_lp_en_dsm_bit_ : coverpoint DFILPCFG0_dfi_lp_en_dsm_bit_8 {
	  option.comment = "This coverpoint covers both the value of field dfi_lp_en_dsm of Register DFILPCFG0";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

	cp_DFILPTMG0_dfi_lp_wakeup_sr_bit_ : coverpoint DFILPTMG0_dfi_lp_wakeup_sr_bit_12_to_8 {
	  option.comment = "This coverpoint covers different values of field dfi_lp_wakeup_sr of Register FDILPTMG0";
    // TODO : Need to cover different combinations
		bins cb_value[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13}; 
	}

	cp_PWRCTL_selfref_sw_bit_ : coverpoint PWRCTL_selfref_sw_bit_11 {
	  option.comment = "This coverpoint covers both the value of field selfref_sw of Register PWRCTL";
    bins cb_logic_0 = {1'b0} iff(PWRCTL_dsm_en_bit_18 == 1);
		bins cb_logic_1 = {1'b1} iff(PWRCTL_dsm_en_bit_18 == 1);
	}

	cp_PWRCTL_selfref_en_bit_ : coverpoint PWRCTL_selfref_en_bit_x {
	  option.comment = "This coverpoint covers both the value of field selref_en of Register PWRCTL";
    bins cb_logic_0 = {1'b0} iff(PWRCTL_dsm_en_bit_18 == 1);
    bins cb_logic_1 = {1'b1} iff(PWRCTL_dsm_en_bit_18 == 1);
	}

	cp_HWLPCTL_hw_lp_en_bit_ : coverpoint HWLPCTL_hw_lp_en_bit_0 {
	  option.comment = "This coverpoint covers both the value of filed hw_lp_en of Register HWLPCTL";
    bins cb_logic_0 = {1'b0} iff(PWRCTL_dsm_en_bit_18 == 1);
    bins cb_logic_1 = {1'b1} iff(PWRCTL_dsm_en_bit_18 == 1);
	}

	cp_DFIPHYMSTR_dfi_phymstr_en_bit_ : coverpoint DFIPHYMSTR_dfi_phymstr_en_bit_0 {
	  option.comment = "This coverpoint covers both the value of field phymstr_en of Register DFIPHYMSTR";
    bins cb_logic_0 = {1'b0} iff(PWRCTL_dsm_en_bit_18 == 1);
    bins cb_logic_1 = {1'b1} iff(PWRCTL_dsm_en_bit_18 == 1);
	}

	//cp_DFIPHYMSTR_dfi_error_bit_ : coverpoint DFIPHYMSTR_dfi_error_bit_ {
	//  option.comment = "This coverpoint covers both the value of field df_error of Register DFIPHYMSTR";
  //  bins cb_logic_0 = {1'b0} iff(PWRCTL_dsm_en_bit_18 == 1);
  //  bins cb_logic_1 = {1'b1} iff(PWRCTL_dsm_en_bit_18 == 1);
	//}

	cp_STAT_selfref_state_bit_ : coverpoint STAT_selfref_state_bit_14_to_12 {
	  option.comment = "This coverpoint covers valid values 'h0 and 'h4 of field selfref_state of Register STAT";
    bins cb_valid_comb_0 = {'h0};
		bins cb_valie_comb_4 = {'h4};
	}

	cp_DFILPTMG0_dfi_lp_wakeup_dsm_bit_ : coverpoint DFILPTMG0_dfi_lp_wakeup_dsm_bit_20_to_16 {
	  option.comment = "This coverpoint covers different values of field dfi_lp_wakeup_sr of Register DFILPTMG0";
		bins cb_value[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13}; 
	}

	cp_DFILPTMG0_dfi_lp_wakeup_pd_bit_ : coverpoint DFILPTMG0_dfi_lp_wakeup_pd_bit_4_to_0 {
	  option.comment = "This coverpoint covers different values of field dfi_lp_wakeup_sr of Register DFILPTMG0";
		bins cb_value[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13}; 
	}

	cp_DFILPTMG0_dfi_lp_wakeup_data_bit_ : coverpoint DFILPTMG1_dfi_lp_wakeup_data_bit_4_to_0 {
	  option.comment = "This coverpoint covers different values of field dfi_lp_wakeup_data of Register DFILPTMG1";
		bins cb_value[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13}; 
	}

	cp_DFILPTMG1_dfi_tlp_resp : coverpoint DFITMG1_dfi_tlp_resp_bit_12_to_8 {
					//TODO : valid values of TLP RESP from phy data book
	} 

endgroup : cg_deep_sleep_mode

//----------------------------------------------------------------------------
// Covergroup Name : cg_selfref_state_coverage
// Arguments       : Field selfref_state of Register STAT 
// Description     : This covergroup covers all possible transitions of field
//                   selfref_state i.e., Entering and Exit from Deep Sleep
//                   Mode and Entering and Exit form Self Refresh State.
//----------------------------------------------------------------------------
covergroup cg_selfref_state_coverage with function sample(bit [2:0] STAT_selfref_state_bit_14_to_12);
  option.per_instance = 1;
  type_option.merge_instances = 0;

	// Covers Entering Deep Sleep Mode
	// Idle => Deep Sleep Mode
	cp_idle_to_deep_sleep_mode : coverpoint STAT_selfref_state_bit_14_to_12 {
	  option.comment = "This coverpoint covers transition of selfref_state form Idle to Deep Sleep Mode";
    bins cb_idle_to_deep_sleep_mode = (3'b000 => 3'b100);
	}
  
	// Covers Entering and Exit from Deep Sleep Mode
	// Idle => Deep Sleep Mode => Self Refresh Power Down => Self Refresh 2 => Idle
	cp_idle_to_deep_sleep_to_idle : coverpoint STAT_selfref_state_bit_14_to_12 {
	  option.comment = "This coverpoint covers transition of selfref_state from Idle to Deep Sleep Mode to Self Refresh Power Down to Self Refresh to Idle";
    bins cb_enter_and_exit_of_deep_sleep_mode = (3'b000 => 3'b100 => 3'b010 => 3'b011 => 3'b000);
	}

	// Idle => Self Refresh Power Down => Self Refresh => Idle
	cp_idle_to_self_ref_pwr_dw_to_self_ref_to_idle : coverpoint STAT_selfref_state_bit_14_to_12 {
	  option.comment = "This coverpoint covers transition of selfref_state from Idle to Self Refresh Power Down to Self Refresh to Idle";
    bins cb_idle_to_sef_ref_pwr_dw_to_idel = (3'b000 => 3'b010 => 3'b011 => 3'b000);
	}

	// Idle => Self Refresh 1 => Self Refresh Power Down => Self Refresh 2 => Idle
	cp_enter_and_exit_from_self_refresh : coverpoint STAT_selfref_state_bit_14_to_12 {
	  option.comment = "This coverpoint covers transition of selfref_state from Idle to Self Refresh 1 to Self Refresh Power Down to Self Refresh 2 to Idle";
    bins cb_enter_and_exit_from_self_refresh = (3'b000 => 3'b001 => 3'b010 => 3'b011 => 3'b000);
	}
endgroup : cg_selfref_state_coverage

// Section Number : 6.4
// Section Name   : Hardware Fast Frequency Change(HWFFC) Test

//----------------------------------------------------------------------------
// Covergroup  : cg_hardware_fsat_frequency_test
// Arguments   : 
// Description : This cvoergroup is for test <Hardware Fast Frequency Change(HWFFC)
//               Test>
//----------------------------------------------------------------------------

covergroup cg_hardware_fast_frequency_test with function sample(bit HWFFCCTL_hwffc_mode_bit_31,
                                                                bit [1:0] HWFFCCTL_hwffc_en_bit_1_to_0,
																															  bit ZQCTL2_dis_srx_zqcl_hwffc_bit_1,	
																																bit csysreq_ddrc,
																																bit csysmode_ddrc,
																																bit csysdiscamdrain_ddrc,
																																bit csysfsp_ddrc,
																																bit csysack_ddrc,
																																bit cactive_ddrc); 

  option.per_instance = 1;
  type_option.merge_instances = 0;

	cp_HWFFCCTL_hwffc_mode_bit_31 : coverpoint HWFFCCTL_hwffc_mode_bit_31 {
	  option.comment = "This coverpoint covers both the value of field hwffcctl_mode of Register HWFFCCTL";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

	cp_HWFFCCTL_hwffc_en_bit_1_to_0 : coverpoint HWFFCCTL_hwffc_en_bit_1_to_0 {
	  option.comment = "This cvoerpoint covers all possible combination of field hwffc_en of Register HWFFCCTL";
    bins cb_00 = {2'b00};  // Disable HWFFC
		bins cb_10 = {2'b10};  // Intermediate
		bins cb_11 = {2'b11};  // Enable legacy HWFFC
	  // Note  : combination 01 is illegal.
	}
  
	cp_ZQCTL2_dis_srx_zqcl_hwffc_bit_1 : coverpoint ZQCTL2_dis_srx_zqcl_hwffc_bit_1 {
	  option.comment = "This coverpoint covers both values of field dis_zrx_zqcl_hwffc of Register ZQCTL2";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1};
	}

  cs_covera_all_combinations : cross cp_HWFFCCTL_hwffc_mode_bit_31,cp_HWFFCCTL_hwffc_en_bit_1_to_0,cp_ZQCTL2_dis_srx_zqcl_hwffc_bit_1 {
	  option.comment = "This cross coverage covers all the possible combinations between HWFFCCTL.hwffc_mode, HWFFCCTL.hwffc_en and ZQCTL2.dis_srx_zqcl_hwffc";
	}

	// coverage for inputs																											
  cp_csysdiscamdrain_ddrc : coverpoint csysdiscamdrain_ddrc {
	  option.comment = "This coverpoint covers both the value of input pin csysdiscamdrain_ddrc when csysreq_ddrc is 0 and csysmode_ddrc is 1";
    bins cb_logic_0 = {1'b0} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	  bins cb_logic_1 = {1'b1} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	}

	cp_csysfsp_ddrc : coverpoint csysfsp_ddrc {
	 option.comment = "This coverpoint covers both the value of input pin csysfsp_ddrc when csysreq_ddrc is 0 and csysmode_ddrc is 1";
    bins cb_logic_0 = {1'b0} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	  bins cb_logic_1 = {1'b1} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	}

	cp_csysack_ddrc : coverpoint csysack_ddrc {
	  option.comment = "This coverpoint covers both the value of input pin csysack_ddrc when csysreq_ddrc is 0 and csysmode_ddrc is 1";
    bins cb_logic_0 = {1'b0} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	  bins cb_logic_1 = {1'b1} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	}

	cp_cactive_ddrc : coverpoint cactive_ddrc {
	  option.comment = "This coverpoint covers both the value of input pin cactive_ddrc when csysreq_ddrc is 0 and csysmode_ddrc is 1";
    bins cb_logic_0 = {1'b0} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	  bins cb_logic_1 = {1'b1} iff(csysreq_ddrc==0 && csysmode_ddrc==1);
	}

endgroup : cg_hardware_fast_frequency_test

// Section Number : 6.5
// Section Name   : LPDDR5 Masked Write Test

//-----------------------------------------------------------------------------
// Covergroup  : cg_lpddr5_masked_write
// Arguments   : 
// Description : This covergroup is for test <LPDDR5 Masked Write Test>
//-----------------------------------------------------------------------------
covergroup cg_lpddr5_masked_write with function sample(bit DFIMISC_IP_optimized_write_bit_7, 
                                                       bit DBICTL_wr_dbi_en_bit_1,
																											 bit DBICTL_dm_en_bit_0,
																											 bit DFIMISC_phy_dbi_mode_bit_1
                                                       );

	cp_DFIMISC_IP_optimized_write_bit_7 : coverpoint DFIMISC_IP_optimized_write_bit_7 {
	  option.comment = "This coverpoint covers both the value of filed IP_optimized_write of Register DFIMISC";
    bins cb_logic_0 = {1'b0};
		bins cb_logic_1 = {1'b1}; // Write DQ will set to 8'hFF
	}

	cp_combination_1 : coverpoint {DFIMISC_IP_optimized_write_bit_7, DBICTL_wr_dbi_en_bit_1, DBICTL_dm_en_bit_0, DFIMISC_phy_dbi_mode_bit_1} {
	  option.comment = "This coverpoint covers different combinations of fields IP_optimized_write, wr_dbi_en, dm_en and phy_dbi_mode";
	  bins cb_comb_1 = {4'b1110};
		bins cb_comb_2 = {4'b0110};
	}

	// TODO : 
	// Note : DBICTL_wr_dbi_en_bit_1 and DBICTL_dm_en_bit_0 are depended on Mode
	// Register values , it has to be same as MR3[7] and MR13[5] respectively. 
endgroup : cg_lpddr5_masked_write
`endif // LPDDR5_SUBSYSTEM_LOW_POWER_AND_POWER_SAVING_FEATURES_COVERGROUPS
