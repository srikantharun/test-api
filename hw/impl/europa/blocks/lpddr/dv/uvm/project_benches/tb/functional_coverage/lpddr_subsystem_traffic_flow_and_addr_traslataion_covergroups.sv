//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_traffic_flow_and_addr_traslataion_covergroups.sv
//---------------------------------------------------------------------------
//Description :
//---------------------------------------------------------------------------
`ifndef LPDDR_SUBSYSTEM_TRAFFIC_FLOW_AND_ADDR_TRASLATAION_COVERGROUPS_SV
`define LPDDR_SUBSYSTEM_TRAFFIC_FLOW_AND_ADDR_TRASLATAION_COVERGROUPS_SV

//-----------------------------------------------------------------------------
// Covergroup Name :
// Description     :
// Arguments       : 1).burst_type
//                   2).
//                   3).
//                   4).
//                   5).
//                   6).
//                   7).
//                   8).
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 2.1 from TP
// burst_type :- AXI4_FIXED    = 2'h0, AXI4_INCR     = 2'h1, AXI4_WRAP     = 2'h2, AXI4_RESERVED = 2'h3
// TODO : Aakash:last 2 section again I need to explore
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
//Section 6 from DDRCTL, 2.1 from TP --> in argument we need to pass AWADDR or ARADDR from AXI
//---------------------------------------------------------------------------------------------
//covergroup system_addr_range with function sample (bit [32:0] aw_or_ar_addr)
//  cp_aw_or_ar_addr : coverpoint aw_or_ar_addr {
//    bins aw_or_ar_addr_range_33b [5]  = {[33'h0_0000_0000 : 44'h1_FFFF_FFFF]};
//    }
//endgroup
// TODO Kunal: address
// TODO Kunal: Error Cases
// TODO Kunal: Reset?
// TODO Kunal: reads and writes
covergroup cg_axi_input_traffic with function sample (
																											bit [1:0] burst_type,
                                                      bit [3:0] burst_size,
																											bit [7:0] burst_length,
																											bit [3:0] qos,
																											bit [32:0] axi_addr, 
																											bit axi_rst_n 
																											);
  option.per_instance = 1;
  type_option.merge_instances = 0;
	cp_axi_rst: coverpoint axi_rst_n {
		bins cb_axi_rst_0 = {1'b0};
		bins cb_axi_rst_1 = {1'b1};
	} 
  cp_burst_type : coverpoint burst_type {
	  bins cb_burst_type_incr 		= {2'b01};
	  bins cb_burst_type_wrap 		= {2'b10};
		illegal_bins cb_burst_rsvd 	= {2'b11};
	}
	cp_burst_size : coverpoint burst_size {
	  bins cb_burst_size [] = {[4'h0:4'h7]};
	}

	cp_qos: coverpoint qos{
		bins cb_qos_b_0 		= {0};
		bins cb_qos_b_low 	= {[1:7]};
		bins cb_qos_b_high 	= {[8:14]};
		bins cb_qos_b_15 		= {15};
	}

  // Coverpoint: write_incr_length
  // Covers the write burst length for incrementing address transactions
  write_incr_length: coverpoint burst_length iff(burst_type == 2'h1)  {

    bins burst_length_1_to_32    = {[0:31]};
    bins burst_length_33_to_64   = {[32:63]};
    bins burst_length_65_to_96   = {[64:95]};
    bins burst_length_97_to_128  = {[96:127]};
    bins burst_length_129_to_160 = {[128:159]};
    bins burst_length_161_to_192 = {[160:191]};
    bins burst_length_193_to_224 = {[192:223]};
    bins burst_length_225_to_256 = {[224:255]};
  }

  // Coverpoint: write_wrap_length
  // Covers the write burst length for wrapped address transactions
  write_wrap_length: coverpoint burst_length iff(burst_type == 2'h2) {
    bins         burst_length_2  = {1};
    bins         burst_length_4  = {3};
    bins         burst_length_8  = {7};
    bins         burst_length_16 = {15};
    //illegal_bins illegal_length  = {0, 2, [4:6], [8:14], [16:$]};
  }

	cp_invalid_length: coverpoint burst_length {
		bins cb_wrap_invalid_length = {0, 2, [4:6], [8:14], [16:$]} iff(burst_type == 2'h2);
	}

	cp_invalid_addr_incr: coverpoint {(axi_addr % 4096 + ((2 ** burst_size) * (burst_length + 1)) > 4096)}{
		option.comment="This coverpoint covers the invalid address for incremental burst i.e. beyond 4KByte boundary";
		bins cb_invalid_addr_incr = {1'b1};
	}

	cp_invalid_addr_wrap: coverpoint (axi_addr % ( 1 << burst_size ) 	!= 0){
		option.comment="This coverpoint covers the invalid address for wrap burst i.e. address unaligned";
		bins cb_invalid_addr_wrap = {1'b1};
	}
endgroup

//-----------------------------------------------------------------------------
// Covergroup Name : cg_address_translation
// Description     :  
// Arguments       : 1-11). ADDRMAPx(x = 0 to 12, except = 1
//                   12). dramset1tmg24
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 2.2 from TP
// TODO : first from TP have doubt
//------------------------------------------------------------------{
covergroup  cg_address_translation with function sample ( 
																													bit [5:0] addrmap0_dch_bit_0,
                                                          bit [5:0] addrmap1_cs_bit_0,
																													bit [5:0] addrmap1_cs_bit_1,
																													bit [5:0] addrmap3_bank_bit_0,
																													bit [5:0] addrmap3_bank_bit_1,
																													bit [5:0] addrmap3_bank_bit_2,
																													bit [5:0] addrmap4_bg_bit_0,
																													bit [5:0] addrmap4_bg_bit_1,
																													bit [4:0] addrmap5_col_bit_10,
																													bit [4:0] addrmap5_col_bit_9,
																													bit [4:0] addrmap5_col_bit_8,
																													bit [4:0] addrmap5_col_bit_7,
																													bit [4:0] addrmap6_col_bit_6,
																													bit [4:0] addrmap6_col_bit_5,
																													bit [4:0] addrmap6_col_bit_4,
																													bit [4:0] addrmap6_col_bit_3,
																													bit [4:0] addrmap7_row_bit_17,
																													bit [4:0] addrmap7_row_bit_16,
																													bit [4:0] addrmap7_row_bit_15,
																													bit [4:0] addrmap7_row_bit_14,
																													bit [4:0] addrmap8_row_bit_13,
																													bit [4:0] addrmap8_row_bit_12,
																													bit [4:0] addrmap8_row_bit_11,
																													bit [4:0] addrmap8_row_bit_10,
																													bit [4:0] addrmap9_row_bit_9,
																													bit [4:0] addrmap9_row_bit_8,
																													bit [4:0] addrmap9_row_bit_7,
																													bit [4:0] addrmap9_row_bit_6,
																													bit [4:0] addrmap10_row_bit_5,
																													bit [4:0] addrmap10_row_bit_4,
																													bit [4:0] addrmap10_row_bit_3,
																													bit [4:0] addrmap10_row_bit_2,
																													bit [4:0] addrmap11_row_bit_1,
																													bit [4:0] addrmap11_row_bit_0,
																													bit addrmap12_bank_hash_en,
																													bit [2:0] addrmap12_nonbinary_device_density,
																													bit [1:0] dramset1tmg24_bank_org,
																													bit lpddr_rank
																												);
  option.per_instance = 1;
  type_option.merge_instances = 0;
  // chanel
  cp_addrmap0_dch_bit_0 : coverpoint addrmap0_dch_bit_0 {
    bins cb_addrmap_dch_bit0 [2] = {[6'd0 : 6'd35], 6'd63 };
    }

	// rank
	cp_addrmap1_cs_bit_0 : coverpoint addrmap1_cs_bit_0 {
    bins cb_addrmap_cs_bit0 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	cp_addrmap1_cs_bit_1 : coverpoint addrmap1_cs_bit_1 {
    bins cb_addrmap_cs_bit1 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	//bank
	cp_addrmap3_bank_bit_0 : coverpoint addrmap3_bank_bit_0 {
    bins cb_addrmap_bank_b0 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	cp_addrmap3_bank_bit_1 : coverpoint addrmap3_bank_bit_1 {
    bins cb_addrmap_bank_b1 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	cp_addrmap3_bank_bit_2 : coverpoint addrmap3_bank_bit_2 {
    bins cb_addrmap_bank_b2 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	//bank group
	cp_addrmap4_bg_bit_0 : coverpoint addrmap4_bg_bit_0 {
    bins cb_addrmap_bg_b0 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	cp_addrmap4_bg_bit_1 : coverpoint addrmap4_bg_bit_1 {
    bins cb_addrmap_bg_b1 [4] = {[6'd0 : 6'd35], 6'd63 };
	}

	//column // TODO :- need to check for x (ECC)
	cp_addrmap5_col_bit_10 : coverpoint addrmap5_col_bit_10 {
    bins cb_addrmap_col_b10 [2] = {[5'd0 : 5'd7], 5'd31 };
	}

	cp_addrmap5_col_bit_9 : coverpoint addrmap5_col_bit_9 {
    bins cb_addrmap_col_b9 [2] = {[5'd0 : 5'd7], 5'd31 };
	}

	cp_addrmap5_col_bit_8 : coverpoint addrmap5_col_bit_8 {
    bins cb_addrmap_col_b8 [2] = {[5'd0 : 5'd7], 5'd31 };
	}

	cp_addrmap5_col_bit_7 : coverpoint addrmap5_col_bit_7 {
    bins cb_addrmap_col_b7 [2] = {[5'd0 : 5'd7], 5'd31 };
	}

	cp_addrmap6_col_bit_6 : coverpoint addrmap6_col_bit_6 {
    bins cb_addrmap_col_b6 [2] = {[5'd0 : 5'd7], 5'd15 };
	}

	cp_addrmap6_col_bit_5 : coverpoint addrmap6_col_bit_5 {
    bins cb_addrmap_col_b5 [2] = {[5'd0 : 5'd7], 5'd15 };
	}

	cp_addrmap6_col_bit_4 : coverpoint addrmap6_col_bit_4 {
    bins cb_addrmap_col_b4 [2] = {[5'd0 : 5'd7], 5'd15 };
	}

	cp_addrmap6_col_bit_3 : coverpoint addrmap6_col_bit_3 {
    bins cb_addrmap_col_b6 [2] = {[5'd0 : 5'd7], 5'd15 };
	}

	// Row
	cp_addrmap7_row_bit_17 : coverpoint addrmap7_row_bit_17 {
    bins cb_addrmap_row_b17 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap7_row_bit_16 : coverpoint addrmap7_row_bit_16 {
    bins cb_addrmap_row_b16 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap7_row_bit_15 : coverpoint addrmap7_row_bit_15 {
    bins cb_addrmap_row_b15 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap7_row_bit_14 : coverpoint addrmap7_row_bit_14 {
    bins cb_addrmap_row_b14 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap8_row_bit_13 : coverpoint addrmap8_row_bit_13 {
    bins cb_addrmap_row_b13 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap8_row_bit_12 : coverpoint addrmap8_row_bit_12 {
    bins cb_addrmap_row_b12 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap8_row_bit_11 : coverpoint addrmap8_row_bit_11 {
    bins cb_addrmap_row_b11 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap8_row_bit_10 : coverpoint addrmap8_row_bit_10 {
    bins cb_addrmap_row_b10 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap9_row_bit_9 : coverpoint addrmap9_row_bit_9 {
    bins cb_addrmap_row_b9 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap9_row_bit_8 : coverpoint addrmap9_row_bit_8 {
    bins cb_addrmap_row_b8 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap9_row_bit_7 : coverpoint addrmap9_row_bit_7 {
    bins cb_addrmap_row_b7 [3] = {[5'd0 : 5'd16], 5'd31 };
	}
	cp_addrmap9_row_bit_6 : coverpoint addrmap9_row_bit_6 {
  	bins cb_addrmap_row_b6 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap10_row_bit_5 : coverpoint addrmap10_row_bit_5 {   //addrmap10_row_bit_5
    bins cb_addrmap_row_b5 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap10_row_bit_4 : coverpoint addrmap10_row_bit_4 {
    bins cb_addrmap_row_b4 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap10_row_bit_3 : coverpoint addrmap10_row_bit_3 {
    bins cb_addrmap_row_b3 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap10_row_bit_2 : coverpoint addrmap10_row_bit_2 {
    bins cb_addrmap_row_b2 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap11_row_bit_1 : coverpoint addrmap11_row_bit_1 {
    bins cb_addrmap_row_b1 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap11_row_bit_0 : coverpoint addrmap11_row_bit_0 {
    bins cb_addrmap_row_b0 [3] = {[5'd0 : 5'd16], 5'd31 };
	}

	cp_addrmap12_bank_hash_en : coverpoint addrmap12_bank_hash_en {
		bins cb_bank_hash_en [] = {1'b0, 1'b1};
  }

	cp_dramset1tmg24 : coverpoint dramset1tmg24_bank_org {
		bins dramset1tmg24_bank_org [] = {2'b00, 2'b10};
	}

	cp_addrmap12_nonbinary_device_density : coverpoint addrmap12_nonbinary_device_density {
		bins nonbinary_device_density [8] = {[3'd0:3'd7]};  // TODO do we need to coevre all 8 or only 5 ?
	}
endgroup  //}

//-----------------------------------------------------------------------------
// Covergroup Name : cg_wcl_clocking
// Description     :  
// Arguments       : 1).DFITMG4
//                   2).DFITMG5
//                   3).TMGCFG
//                   4).MSTR4
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 2.3 from TP
//------------------------------------------------------------------
covergroup cg_wcl_clocking with function sample (bit [31:0] dfitmg4,
                                                 bit [31:0] dfitmg5,
																								 bit tmgcfg_frequency_ratio,
																								 bit mstr4_wck_on,
																								 bit mstr4_wck_suspend_en,
																								 bit mstr4_ws_off_en/*,
																								 bit perf_op_is_cas_ws,
																								 bit perf_op_is_cas_ws_off,
																								 bit perf_op_is_cas_wck_sus*/);
  option.per_instance = 1;
  type_option.merge_instances = 0;

  cp_dfitmg4_1 : coverpoint dfitmg4 {
		bins cb_dfitmg4_1 = {[32'h00000000:32'h3FFFFFFF]};
		bins cb_dfitmg4_2 = {[32'h40000000:32'h7FFFFFFF]};
		bins cb_dfitmg4_3 = {[32'h80000000:32'hBFFFFFFF]};
		bins cb_dfitmg4_4 = {[32'hC0000000:32'hFFFFFFFF]};
	}
  cp_dfitmg5_1 : coverpoint dfitmg5 {
		bins cb_dfitmg5_1 = {[32'h00000000:32'h3FFFFFFF]};
		bins cb_dfitmg5_2 = {[32'h40000000:32'h7FFFFFFF]};
		bins cb_dfitmg5_3 = {[32'h80000000:32'hBFFFFFFF]};
		bins cb_dfitmg5_4 = {[32'hC0000000:32'hFFFFFFFF]};
	}
	cp_tmgcfg : coverpoint tmgcfg_frequency_ratio {
		bins cb_tmgcfg_frequency_ratio = {1'b1};
	}
	cp_mstr4_bit_0 : coverpoint mstr4_wck_on {
		bins cb_mstr4_wck_on [] = {1'b0, 1'b1};
	}
	cp_mstr4_bit_4 : coverpoint mstr4_wck_suspend_en iff (mstr4_wck_on == 1){
		bins cb_mstr4_wck_suspend_en [] = {1'b0, 1'b1};
	}
	cp_mstr4_bit_8 : coverpoint mstr4_ws_off_en iff (mstr4_wck_on == 1){
		bins cb_mstr4_ws_off_en [] = {1'b0, 1'b1};
	}
	
	//cp_perf_op_is_cas_ws : coverpoint perf_op_is_cas_ws {
	//	bins cb_perf_op_is_cas_ws [] = {1'b0, 1'b1};
	//}
	//cp_perf_op_is_cas_ws_off : coverpoint perf_op_is_cas_ws_off {
	//	bins cb_perf_op_is_cas_ws_off [] = {1'b0, 1'b1};
	//}
	//cp_perf_op_is_cas_wck_sus : coverpoint perf_op_is_cas_wck_sus {
	//	bins cb_perf_op_is_cas_wck_sus [] = {1'b0, 1'b1};
	//}
endgroup : cg_wcl_clocking

//-----------------------------------------------------------------------------
// Covergroup Name : cg_pagematch
// Description     :
// Arguments       : 1).PCFGW.rd_port_pagematch_en
//                   2).PCFGR.wr_port_pagematch_en
//                   3).PCCFG.pagematch_limit
//                   4).
//                   5).
//                   6).
//                   7).
//                   8).
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 2.4 from TP
// TODO : last 3 point need to read
//----------------------------------------------------------------------------
covergroup cg_pagematch with function sample (bit pcfgw_wr_port_pagematch_en,
																							bit pcfgr_rd_port_pagematch_en,
																							bit pccfg_pagematch_limit, 
																							bit [32:0] axi_addr);
  option.per_instance = 1;
  type_option.merge_instances = 0;
  cp_pcfgr_rd_port_pagematch_en : coverpoint pcfgr_rd_port_pagematch_en {
	  bins cb_pcfgr_rd_port_pagematch_en [] = {1'b0, 1'b1};
	}

	cp_pcfgw_wr_port_pagematch_en : coverpoint pcfgw_wr_port_pagematch_en {
	  bins cb_pcfgw_wr_port_pagematch_en [] = {1'b0, 1'b1};
	}

	cp_pccfg_pagematch_limit : coverpoint pccfg_pagematch_limit {
	  bins cb_pccfg_pagematch_limit [] = 	{1'b0, 1'b1};
	}
// TODO Kunal: add; this cp
	//cp_axi_addr : coverpoint axi_addr{
		//option.comment="This coverpoint covers that the stimulus drives continously on the same page addresses";
		//cb_same_addr_trans={};
	//}
endgroup

//-----------------------------------------------------------------------------
// Covergroup Name : cg_axi_rd_wr
// Description     :
// Arguments       : 1).
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 2.5 from TP
// TODO :
//----------------------------------------------------------------------------
covergroup throughput_test with function sample ( bit axi_rd_or_wr,
                                                  bit [3:0] axi_qos,
																								  bit [3:0] axi_size,
																								  bit [7:0] axi_burst_length,
																									bit [32:0] axi_addr);
  option.per_instance = 1;
  type_option.merge_instances = 0;
	cp_axi_qos : coverpoint axi_qos {
    bins cb_axi_qos [] = {[4'h0:4'hf]};
	}

// TODO : need to re-enable below code
//	cp_axi_addr : coverpoint axi_addr {
//	  bins cb_axi_addr [] = {};
//	}
endgroup

//-----------------------------------------------------------------------------
// Covergroup Name : cg_axi_rd_wr
// Description     :
// Arguments       : 1).
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 2.6 from TP
// TODO :
//-------------------------------------------------------------------------------
covergroup cg_transaction_poisoning_test with function sample (bit poison,
																															 bit poisoncfg_posion_slverr_en,
																															 bit poisoncfg_poison_intr_en,
																															 bit poisoncfg_poison_intr_clr,
																															 bit poisonstat_poison_intr_0);
  option.per_instance = 1;
  type_option.merge_instances = 0;

	cp_poison : coverpoint poison {
		bins bin_poison [] = {1'b0, 1'b1};
	}
	cp_posion_slverr_en : coverpoint poisoncfg_posion_slverr_en {
    bins cb_posion_slverr_en [] = {1'b0, 1'b1};
	}
	cp_poison_intr_en : coverpoint poisoncfg_poison_intr_en {
		bins cb_poison_intr_en [] = {1'b0, 1'b1};
	}
	cp_poison_intr_clr : coverpoint poisoncfg_poison_intr_clr {
		bins cb_poison_intr_clr [] = {1'b0, 1'b1};
	}
  cp_poisonstat_poison_intr_0 : coverpoint poisonstat_poison_intr_0 {
	  bins cb_poisonstat_poison_intr_0 [] = 	{1'b0, 1'b1};
	}
endgroup : cg_transaction_poisoning_test

`endif // LPDDR_SUBSYSTEM_TRAFFIC_FLOW_AND_ADDR_TRASLATAION_COVERGROUPS_SV
