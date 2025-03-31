//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_initialization_covergroups.sv 
//---------------------------------------------------------------------------
//Description :
//---------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_INITIALZATION_COVERGROUOS_SV
`define LPDDR_SUBSYSTEM_INITIALZATION_COVERGROUOS_SV

//-----------------------------------------------------------------------------
// Covergroup Name : cg_initalization_reg
// Arguments       : inittmg0_skip_dram_init, core_ddrc_rstn, Reset_async,
//                   Reset, dfimisc_dfi_init_start, dfistat_dfi_init_complete,
//                   stat_operating_mode, mstr0_burst_rdwr, mstr0_data_bus_width,
//                   mstr0_active_ranks
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 1.1 from TP
//-----------------------------------------------------------------------------
covergroup cg_initalization_reg with function sample (bit[1:0] inittmg0_skip_dram_init,
                                                      bit core_ddrc_rstn,
                                                      bit Reset_async,
																                      bit Reset,
																                      bit dfimisc_dfi_init_start,
																                      bit dfistat_dfi_init_complete,
																                      bit [2:0] stat_operating_mode,
																                      bit [4:0] mstr0_burst_rdwr,
																                      bit [1:0] mstr0_data_bus_width,
                                                      bit [1:0] mstr0_active_ranks);
  option.per_instance = 1;
  type_option.merge_instances = 0;

	cp_skip_dram_init : coverpoint inittmg0_skip_dram_init {
		bins cb_inittmg0_skip_dram_init [] = {2'b00, 2'b01, 2'b11};
	}

	cp_core_ddrc_rstn : coverpoint core_ddrc_rstn {
	  bins cb_core_ddrc_rstn [] = {1'b0, 1'b1};
	}

	cp_phy_reset_async : coverpoint Reset_async {
	  bins cb_phy_reset_async [] = {1'b0, 1'b1};
	}

	cp_phy_reset : coverpoint Reset {
	  bins cb_phy_reset [] = {1'b0, 1'b1};
	}
	
	cp_dfimisc_dfi_init_start : coverpoint dfimisc_dfi_init_start {
		bins cb_dfimisc_dfi_init_start [] = {1'b0, 1'b1};
	}
	
	cp_dfistat_dfi_init_complete : coverpoint dfistat_dfi_init_complete {
		bins cb_dfistat_dfi_init_complete [] = {1'b0, 1'b1};
	}
	
	cp_stat_operating_mode : coverpoint stat_operating_mode {
	  bins cb_stat_operating_mode = {3'b001};
	}

	cp_mstr0_burst_rdwr : coverpoint mstr0_burst_rdwr {
	  bins cb_mstr0_burst_rdwr = {5'b01000};
	}
	
	cp_mstr0_data_bus_width : coverpoint mstr0_data_bus_width {
	  bins cb_mstr0_data_bus_width[] = {2'b00, 2'b01};
	}
	
	cp_mstr0_active_ranks : coverpoint mstr0_active_ranks {
	  bins cb_mstr0_active_ranks[] = {2'b01, 2'b11};
	}
endgroup : cg_initalization_reg

//-----------------------------------------------------------------------------
// Covergroup Name : cg_apb_address_decoding
// Description     :  
// Arguments       : 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 1.2 from TP 
//-----------------------------------------------------------------------------
covergroup cg_apb_address_decoding with function sample ( bit [31:0] apb_paddr,
                                                          bit apb_pwrite,
																													bit apb_presetn
																												);
  option.per_instance = 1;
	type_option.merge_instances = 0;
  cp_apb_paddr_bit_25 : coverpoint apb_paddr[25] {
	  bins cb_apb_paddr_bit_25_write [1] = {1'b0} iff(apb_pwrite == 1);
	  bins cb_apb_paddr_bit_25_read [1] = {1'b0} iff(apb_pwrite == 0);

	}

	cp_apb_paddr_bit_25_22 : coverpoint apb_paddr[25:22] {
	  bins cb_apb_paddr_bit_25_22_write_1 [1] = {4'b1000} iff(apb_pwrite == 1);
	  bins cb_apb_paddr_bit_25_22_write_0 [1] = {4'b1000} iff(apb_pwrite == 0);
	}

	cp_apb_presetn : coverpoint apb_presetn {
	  bins cb_apb_presetn_0_to_1 = (0 => 1);	
	  bins cb_apb_presetn_1_to_0 = (1 => 1);	
	}
endgroup

/*//covergroup for checking paddr[25:22]
covergroup cg_paddr_25_22();
  option.per_instance = 1;
	option.merge_instance = 0;
  cp_paddr_25_22 : coverpoint trans_apb.paddr[25:22] {
		bins all_combanation = {[4'h0:4'hF]};
		}
endgroup */

//-----------------------------------------------------------------------------
// Covergroup Name : cg_mode_reg_rd_wr
// Description     :  
// Arguments       : mrctrl0_mr_rank, mrctrl0_mr_addr, mrctrl1_mr_data,
//									 hif_mrr_data, hif_mrr_data_valid, mrctrl0_mr_type,
//                   mrctrl0_mrr_done_clr, mrstat_mrr_done.
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 1.3 from TP
//-----------------------------------------------------------------------------
covergroup cg_mode_reg_rd_wr with function sample (bit [1:0] mrctrl0_mr_rank,
                                                   bit [3:0] mrctrl0_mr_addr,
                                                   bit [17:0] mrctrl1_mr_data,
																									 bit [31:0] hif_mrr_data,
																									 bit hif_mrr_data_valid,
																									 bit mrctrl0_mr_type,
                                                   bit mrctrl0_mrr_done_clr,
                                                   bit mrstat_mrr_done);
  option.per_instance = 1;
	type_option.merge_instances = 0;
	
  cp_mrctrl0_mr_rank : coverpoint mrctrl0_mr_rank {
    bins cb_mrctrl0_mr_rank [] = {2'b01, 2'b10};
	}
	cp_mrctrl0_mr_addr : coverpoint mrctrl0_mr_addr {
    bins cb_mrctrl0_mr_addr [] = {4'b0000, 4'b0001, 4'b0010, 4'b0011, 4'b0100, 4'b0101, 4'b0110, 4'b0111};
	}
	cp_mrctrl0_mr_type : coverpoint mrctrl0_mr_type {
	  bins cb_mrctrl0_mr_type [] = {1'b0, 1'b1};
	}
  cp_mrctrl0_mrr_done_clr : coverpoint mrctrl0_mrr_done_clr {
	  bins cb_mrctrl0_mrr_done_clr [] = {1'b0, 1'b1};
	}
  cp_mrstat_mrr_done : coverpoint mrstat_mrr_done {
	  bins cb_mrstat_mrr_done [] = {1'b0, 1'b1};
	}
	cp_mrctrl1_mr_data : coverpoint mrctrl1_mr_data {
		bins cb_mr_data_1 = {[17'h00000:17'h07FFF]};
		bins cb_mr_data_2 = {[17'h08000:17'h0FFFF]};
		bins cb_mr_data_3 = {[17'h10000:17'h17FFF]};
		bins cb_mr_data_4 = {[17'h18000:17'h1FFFF]};
	}
  cp_hif_mrr_data : coverpoint hif_mrr_data iff (hif_mrr_data_valid == 1){
		bins cb_hif_mrr_data_1 = {[32'h00000000:32'h3FFFFFFF]};
		bins cb_hif_mrr_data_2 = {[32'h40000000:32'h7FFFFFFF]};
		bins cb_hif_mrr_data_3 = {[32'h80000000:32'hBFFFFFFF]};
		bins cb_hif_mrr_data_4 = {[32'hC0000000:32'hFFFFFFFF]};
	}
endgroup : cg_mode_reg_rd_wr

//-----------------------------------------------------------------------------
// Covergroup Name : cg_data_bus_inversion
// Description     :  
// Arguments       : 1).DFIMISC (field : phy_dbi_mode)
//                   2).DBICTL
//                   3). 
//                   4). 
//                   5). 
//                   6). 
//                   7). 
//                   8). 
// Reference       : DWC_ddrctl_lpddr54_lpddr5x_referenct.pdf, 1.4 from TP
// TODO : que - what is data value in TP ?
//-----------------------------------------------------------------------------
covergroup cg_data_bus_inversion with function sample(/*bit [255:0] data[],
                                                     */ bit dfimisc_phy_dbi_mode,
                                                      bit dbictl_dbi_en,
																											bit dbictl_dm_en);
  option.per_instance = 1;
	type_option.merge_instances = 0;
  		
  cp_dbictl_dbi_dm_en_less_than_4 :coverpoint {dbictl_dbi_en,dbictl_dm_en,(dfimisc_phy_dbi_mode==0)/*,($countones(data[i]) < 4)*/} { 
		bins cb_dbictl_dbi_en_0 = {'b001};
		bins cb_dbictl_dbi_en_1 = {'b011};
		bins cb_dbictl_dbi_en_2 = {'b101};
		bins cb_dbictl_dbi_en_3 = {'b111};
	}

	cp_dbictl_dbi_dm_en_more_than_4 :coverpoint {dbictl_dbi_en,dbictl_dm_en,(dfimisc_phy_dbi_mode==0)/*,($countones(data[i]) > 4)*/} { 
		bins cb_dbictl_en_0 = {'b001};
		bins cb_dbictl_en_1 = {'b011};
		bins cb_dbictl_en_2 = {'b101};
		bins cb_dbictl_en_3 = {'b111};
	}
endgroup : cg_data_bus_inversion
`endif // LPDDR_SUBSYSTEM_INITIALZATION_COVERGROUOS_SV
