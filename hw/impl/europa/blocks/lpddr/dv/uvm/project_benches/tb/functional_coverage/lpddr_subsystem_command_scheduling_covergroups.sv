//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_command_scheduling_covergroups.sv
//---------------------------------------------------------------------------
//Description :
// TODO Kunal: modify; update all the headers
//---------------------------------------------------------------------------
`ifndef LPDDR_SUBSYSTEM_COMMAND_SCHEDULING_COVERGROUPS_SV
`define LPDDR_SUBSYSTEM_COMMAND_SCHEDULING_COVERGROUPS_SV

//-----------------------------------------------------------------------------
// Covergroup Name : cg_page_policy
// Description     :  
//                   
//                   
// Arguments       : 1).SCHED0
//                   2).SCHEDTMG0
//                   3).a10_a0 (from lppdr trans)
//                   4). 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 3.1 from TP
// TODO : que - on which signal AXI read/write can be cover ? 
//-----------------------------------------------------------------------------

covergroup cg_page_policy with function sample ( bit sched0_pageclose, 
                                                 bit [7:0] schedtmg0_pageclose_timer,
																								 bit a10_a0
																							 );
  option.per_instance = 1;
	type_option.merge_instances = 0;

	cp_pageclose : coverpoint sched0_pageclose {
		bins cb_sched0_pageclose [] = {1'b0, 1'b1};
	}

	cp_pageclose_timer : coverpoint schedtmg0_pageclose_timer iff(sched0_pageclose) {
		bins cb_schedtmg0_pageclose_timer [5] = {[8'd1:8'd50],[8'd51:8'd100],[8'd101:8'd150],[8'd151:8'd200],[8'd201:8'd255] };
	}
	
  //cp_cross_pageclose_X_pageclose_timer : cross cp_pageclose, cp_pageclose_timer;

	cp_a10_ap_1 : coverpoint a10_a0 iff(sched0_pageclose && (schedtmg0_pageclose_timer == 0)) {
		bins cb_a10_ap_1 = {'b1};
	}

	cp_a10_ap_0 : coverpoint a10_a0 iff(sched0_pageclose && (schedtmg0_pageclose_timer > 0)) {
		bins cb_a10_ap_0 = {'b0};
	}
	
endgroup

//-----------------------------------------------------------------------------
// Covergroup Name : cg_wr_to_rd_switching
// Description     :  
//                   
//                   
// Arguments       : 1).PCFGQOS0.RQOS_MAP_LEVEL1
//                   2).PCFGWQOS0
//                   3).SCHED4
//                   4). 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 3.2 from TP
//-----------------------------------------------------------------------------	
// TODO Kunal: remove? re-implemented
//covergroup cg_wr_to_rd_switching with function sample ( bit [3:0] pcfgqos0_rqos_map_level1,
//                                                        bit [2:0] pcfgqos0_rqos_map_level2,
//																												bit [1:0] pcfgqos0_rqos_map_region0,
//																												bit [1:0] pcfgqos0_rqos_map_region1,
//																												bit [1:0] pcfgqos0_rqos_map_region3,
//																												bit [3:0] pcfgwqos0_wqos_map_level1,
//																												bit [2:0] pcfgwqos0_wqos_map_level2,
//																												bit [2:0] pcfgwqos0_wqos_map_region0,
//																												bit [2:0] pcfgwqos0_wqos_map_region1,
//																												bit [2:0] pcfgwqos0_wqos_map_region2,
//																												bit [9:0] pcfgqos1_rqos_map_timeoutb,  //TODO :- for this 6 what is the timeout value will program ?
//																												bit [9:0] pcfgqos1_rqos_map_timeoutr,
//																												bit [9:0] pcfgwqos1_wqos_map_timeout1,
//																												bit [9:0] pcfgwqos1_wqos_map_timeout2,
//																												bit [7:0] sched4_rd_page_exp_cycles,  //put with iff
//																												bit [7:0] sched4_wd_page_exp_cycles,  //write with iff
//																												bit [5:0] sched3_wrcam_lowthresh, 
//																												bit [5:0] sched3_wrcam_highthresh,
//																												bit [3:0] axi_qos,
//																												bit axi_read_or_write
//
//																											);
//  option.per_instance = 1;
//	type_option.merge_instances = 0;
//  cp_pcfgqos0_rqos_map_level1 : coverpoint pcfgqos0_rqos_map_level1 {
//	  bins cb_pcfgqos0_rqos_map_level1 [3] = {[4'd0:4'd14]};
//	}
//
//	cp_pcfgqos0_rqos_map_level2 : coverpoint pcfgqos0_rqos_map_level2 {
//		bins cb_pcfgqos0_rqos_map_level2 [2] = {[3'd0:3'd7]};           // TODO : need to understand correct range
//	}
//
//	cp_pcfgqos0_rqos_map_region0 : coverpoint pcfgqos0_rqos_map_region0 {
//	  bins cb_pcfgqos0_rqos_map_region0 [3] = {2'd0, 2'd1, 2'd2}; // 0-LPR, 1-VPR, 2-HPR
//	}
//
//  cp_pcfgqos0_rqos_map_region1 : coverpoint pcfgqos0_rqos_map_region1 {
//	  bins cb_pcfgqos0_rqos_map_region1 [3] = {2'd0, 2'd1, 2'd2}; // 0-LPR, 1-VPR, 2-HPR
//	}
//
//	cp_pcfgqos0_rqos_map_region3 : coverpoint pcfgqos0_rqos_map_region3 {
//	  bins cb_pcfgqos0_rqos_map_region3 [2] = {2'd0, 2'd1}; // 0-VPR, 1-HPR only
//	}
//	
//	cp_pcfgwqos0_wqos_map_level1 : coverpoint pcfgwqos0_wqos_map_level1 {
//	  bins cb_pcfgwqos0_wqos_map_level1 [3] = {[4'd0:4'd13]};
//	}
//	
//	cp_pcfgwqos0_wqos_map_level2 : coverpoint pcfgwqos0_wqos_map_level2 {
//	  bins cb_pcfgwqos0_wqos_map_level2 [3] = {[3'd0:3'd7]};
//	}
//
//	cp_pcfgwqos0_wqos_map_region0 : coverpoint pcfgwqos0_wqos_map_region0 {
//	  bins cb_pcfgwqos0_wqos_map_region0 [2] = {2'd0, 2'd1};	
//	}
//
//	cp_pcfgwqos0_wqos_map_region1 : coverpoint pcfgwqos0_wqos_map_region1 {
//	  bins cb_pcfgwqos0_wqos_map_region1 [2] = {2'd0, 2'd1};	
//	}
//
//	cp_pcfgwqos0_wqos_map_region2 : coverpoint pcfgwqos0_wqos_map_region2 {
//	  bins cb_pcfgwqos0_wqos_map_region2 [2] = {2'd0, 2'd1};	
//	}
//
//	cp_axi_qos : coverpoint axi_qos {
//	  bins cb_axi_qos [] = {[4'd0:4'd15]};
//	}
//
//	cp_axi_read_or_write : coverpoint axi_read_or_write {
//	  bins cb_axi_read_or_write [2] = {1'b0, 1'b1};
//	}
//  
//	cp_cross_axi_qos_X_axi_read_or_write : cross axi_qos, axi_read_or_write;
//	
//
//endgroup 
covergroup cg_wr_to_rd_switching with function sample ( bit [31:0] PCFGQOS0,
																												bit [31:0] PCFGQOS1,
																												bit [31:0] PCFGWQOS0,
																												bit [31:0] PCFGWQOS1,
																												bit [31:0] SCHED4,
																												bit [31:0] SCHED3,
																												bit [3:0] axi_qos,
																												axi4_rw_e axi_read_or_write);

  option.per_instance = 1;
	type_option.merge_instances = 0;

  cp_pcfgqos0_rqos_map_level1 : coverpoint PCFGQOS0[3:0]{
	  bins cb_pcfgqos0_rqos_map_level1 [3] = {[4'd0:4'd14]};
	}

	cp_pcfgqos0_rqos_map_level2 : coverpoint PCFGQOS0[12:8]{
		bins cb_pcfgqos0_rqos_map_level2 [2] = {[4'd1:4'd15]};  
	}

	cp_pcfgqos0_rqos_map_region0 : coverpoint PCFGQOS0[17:16]{
	  bins cb_pcfgqos0_rqos_map_region0_lpr = {0};
	  bins cb_pcfgqos0_rqos_map_region0_vpr = {1};
	  bins cb_pcfgqos0_rqos_map_region0_hpr = {2};
	}

  cp_pcfgqos0_rqos_map_region1 : coverpoint PCFGQOS0[21:20]{
	  bins cb_pcfgqos0_rqos_map_region1_lpr = {0}; 
	  bins cb_pcfgqos0_rqos_map_region1_vpr = {1}; 
	  bins cb_pcfgqos0_rqos_map_region1_hpr = {2}; 
	}

  cp_pcfgqos0_rqos_map_region2 : coverpoint PCFGQOS0[25:24]{
	  bins cb_pcfgqos0_rqos_map_region1_vpr = {1};
	  bins cb_pcfgqos0_rqos_map_region1_hpr = {2};
	}

  cp_pcfgwqos0_wqos_map_level1 : coverpoint PCFGWQOS0[3:0]{
	  bins cb_pcfgwqos0_wqos_map_level1 [3] = {[4'd0:4'd13]};
	}

	cp_pcfgwqos0_wqos_map_level2 : coverpoint PCFGWQOS0[12:8]{
		bins cb_pcfgwqos0_wqos_map_level2 [2] = {[4'd1:4'd15]};  
	}

	cp_pcfgwqos0_wqos_map_region0 : coverpoint PCFGWQOS0[17:16]{
	  bins cb_pcfgwqos0_wqos_map_region0_npw = {0};
	  bins cb_pcfgwqos0_wqos_map_region0_vpw = {1};
	}

  cp_pcfgwqos0_wqos_map_region1 : coverpoint PCFGWQOS0[21:20]{
	  bins cb_pcfgwqos0_wqos_map_region1_npw = {0}; 
	  bins cb_pcfgwqos0_wqos_map_region1_vpw = {1}; 
	}

  cp_pcfgwqos0_wqos_map_region2 : coverpoint PCFGWQOS0[25:24]{
	  bins cb_pcfgwqos0_wqos_map_region1_npw = {0};
	  bins cb_pcfgwqos0_wqos_map_region1_vpw = {1};
	}

  cp_pcfgqos1_rqos_map_timeoutb : coverpoint PCFGQOS1[10:0]{
		bins cb_pcfgqos1_rqos_map_timeoutb[10] = {[0:2048]};
	}

  cp_pcfgqos1_rqos_map_timeoutr : coverpoint PCFGQOS1[26:16]{
		bins cb_pcfgqos1_rqos_map_timeoutr[10] = {[0:2048]};
	}

  cp_pcfgwqos1_wqos_map_timeout1 : coverpoint PCFGWQOS1[10:0]{
		bins cb_pcfgwqos1_wqos_map_timeout1[10] = {[0:2048]};
	}

  cp_pcfgwqos1_wqos_map_timeout2 : coverpoint PCFGWQOS1[26:16]{
		bins cb_pcfgwqos1_wqos_map_timeout2[10] = {[0:2048]};
	}

	cp_sched4_rd_act_idle_gap : coverpoint SCHED4[7:0]{
		bins cb_sched4_rd_act_idle_gap[4]= {[0:255]};
	}

	cp_sched4_wr_act_idle_gap : coverpoint SCHED4[15:8]{
		bins cb_wr_act_idle_gap[4]= {[0:255]};
	}

	cp_sched4_rd_page_exp_cycles : coverpoint SCHED4[23:16]{
		bins cb_rd_page_exp_cycles[4]= {[0:255]};
	}

	cp_sched4_wr_page_exp_cycles : coverpoint SCHED4[31:24]{
		bins cb_wr_page_exp_cycles[4]= {[0:255]};
	}

	cp_sched3_wrcam_lowthresh : coverpoint SCHED3[5:0]{
		bins cb_wrcam_lowthresh[4]={[0:63]};
	}

	cp_sched3_wrcam_highthresh : coverpoint SCHED3[13:8]{
		bins cb_wrcam_highthresh[4]={[0:63]};
	}

	cp_qos: coverpoint axi_qos{
		bins cb_qos_b_0 		= {0};
		bins cb_qos_b_low 	= {[1:7]};
		bins cb_qos_b_high 	= {[8:14]};
		bins cb_qos_b_15 		= {15};
	}

 cp_axi_read_or_write: coverpoint axi_read_or_write{
 	bins cb_axi_read= {AXI4_TRANS_READ};
  bins cb_axi_write= {AXI4_TRANS_WRITE};
 }
endgroup:cg_wr_to_rd_switching
																												
//-----------------------------------------------------------------------------
// Covergroup Name : cg_addr_collision_handling
// Description     :  
//                   
//                   
// Arguments       : 1).
//                   2).
//                   3).
//                   4). 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 3.3 from TP
//-----------------------------------------------------------------------------
covergroup cg_addr_collision_handling with function sample(	bit read_or_write,
																														bit [32:0] addr,
																														bit opctrl0_dis_wc, 
																														bit ecccfg0_ecc_mode,
																														bit dbictl_dm_en);
	option.per_instance = 1;
	type_option.merge_instances = 0;
	
	cp_dis_wc: coverpoint opctrl0_dis_wc {
		option.comment="";

		bins cb_dis_wc_0 = {1'b0};
		bins cb_dis_wc_1 = {1'b1};
	}
	cp_new_read_queued_read: coverpoint read_or_write{
		option.comment="This coverpoint verifies the new read queued read scenario";

		bins cb_new_read_queued_read 				= {1'b0->1'b0};
	} 

	cp_new_write_queued_write: coverpoint read_or_write{
		option.comment="This coverpoint verifies the new write queued write scenario";

		bins cb_new_write_queued_write		 	= {1'b1 -> 1'b1};
	}

	cp_new_read_queued_write: coverpoint read_or_write {
		option.comment="This coverpoint verifies the new read queued write scenario";

		bins cb_new_read_queued_write 			= {1'b1->1'b0};
	
	}

	cp_new_write_queued_read: coverpoint read_or_write {
		option.comment="This coverpoint verifies the new read queued write scenario";

		bins cb_new_write_queued_read 			= {1'b0->1'b1};
	
	}

//	cp_new_read_queued_rmw: coverpoint {read_or_write,axi_wrap_size} {
//		option.comment="This coverpoint verifies the new read colliding with both read and write scenario";
//
//		bins cb_new_read_queued_rmw 			= {1'b0->1'b1};
//	
//	}

	cross_new_write_queued_write_dis_wc: cross cp_new_write_queued_write,cp_dis_wc{
		option.comment ="This cross covers new write after queued write with write combine turned on and off";
	}
	
endgroup:cg_addr_collision_handling
//-----------------------------------------------------------------------------
// Covergroup Name : 
// Description     :  
//                   
//                   
// Arguments       : 1).PCFGR
//                   2).SCHED0
//                   3).
//                   4). 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 3.4 from TP
// TODO : did not found hpr_num signal
//-----------------------------------------------------------------------------
covergroup cg_ddrc_rd_wr_internal_port_priorities with function sample ( bit [9:0] pcfgr_rd_port_priority, 
                                                                         bit [9:0] pcfgw_wr_port_priority,
																																				 bit [5:0] sched0_lpr_num_entries,
																																				 bit dbictl_dm_en, 
																																				 bit [7:0] axi_burst_length
																																			 );
  option.per_instance = 1;
	type_option.merge_instances = 0;

  cp_sched0_lpr_num_entries : coverpoint sched0_lpr_num_entries {
	  bins cb_sched0_lpr_num_entries [4] = {6'd0,[6'd1:6'd62],6'd63};	
	}
 //TODO Kunal:
	//cp_hpr_num_entries : coverpoint (MEMC_NO_OF_ENTRY-(sched0_lpr_num_entries +1)){ 
	//}
 //TODO Kunal: add; coverpoint for axi burst length     
 //TODO Kunal: modify; add bin for hpr_num_entries as well 
endgroup 



//---------------------------------------------------------------------------------------------
//3.1 from TP 
//---------------------------------------------------------------------------------------------
covergroup commands_executed_out_of_order with function sample ( bit pcfgr_rdwr_ordered_en );
  option.per_instance = 1;
	type_option.merge_instances = 0;
	cp_pcfgr : coverpoint pcfgr_rdwr_ordered_en {
		bins pcfgr_rdwr_ordered_en [] = {1'b0, 1'b1};
	}
endgroup

`endif // LPDDR_SUBSYSTEM_COMMAND_SCHEDULING_COVERGROUPS_SV

