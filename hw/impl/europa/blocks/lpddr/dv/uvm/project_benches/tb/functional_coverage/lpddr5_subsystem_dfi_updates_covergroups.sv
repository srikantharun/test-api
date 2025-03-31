`ifndef LPDDR5_SUBSYSTEM_DFI_UPDATES_COVERGROUPS
`define LPDDR5_SUBSYSTEM_DFI_UPDATES_COVERGROUPS

class lpddr5_subsystem_dfi_updates_covergroups extends uvm_component;

  //----------------------------------------------------------------------------
  // Register with factory
  //----------------------------------------------------------------------------
  `uvm_component_utils(lpddr5_subsystem_dfi_updates_covergroups)

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments     : string name
  //                 uvm_component parent
  //----------------------------------------------------------------------------
  function new ( string name = "lpddr5_subsystem_dfi_updates_covergroups", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  //----------------------------------------------------------------------------
  // Function Name : build_phase
  // Arguments     : uvm_phase phase
  //----------------------------------------------------------------------------
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
  endfunction: build_phase

  //----------------------------------------------------------------------------
  // Function Name : connect_phase
  // Arguments     : uvm_phase phase
  //----------------------------------------------------------------------------
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
  endfunction: connect_phase    

  // Section Number : 8.1
  // Section Name   : DFI Updates Mode Test
  
  //-----------------------------------------------------------------------------
  // Covergroup Name : cg_dif_updates_mode
  // Arguments       : Following Registers fields are input to this covergroup 
  //                   1. OPCTRLCMD
  //                   2. OPCTRLSTAT
  //                   3. DFIUPDO
  //                   4. DIFTMG0
  //                   5. DFIUPDTMG0
  //                   6. DFIUPDTMG1
  //                   7. DFIUPDTMG2
  //                   8. DFIUPDTMG3
  // Description     : This covergroup is for test case <DFI Updates Mode Test>
  //                   which covers different values of Registers mentioned 
  //                   above.
  //-----------------------------------------------------------------------------
  covergroup cg_dfi_updates_mode with function sample(bit OPCTRLCMD_ctrlupdp_bit_17,
                                                      bit DFIUPD0_dis_auto_ctrlupd_bit_31,
  																								    bit OPCTRLSTAT_ctrlupd_busy_bit_16,
  																										bit	DFIUPD0_dif_phyupd_en_bit_15,
  																										bit [4:0]	DFITMG0_dfi_t_ctrl_delay_bit_28_to_24,
                                                      bit [9:0] DFIUPDTMG0_dfi_t_ctrlup_min_bit_9_to_0,
                                                      bit [9:0] DFIUPDTMG0_dfi_t_ctrlup_max_bit_25_to_16,
  																										bit [7:0] DFIUPDTMG1_dfi_t_ctrlup_interval_min_x1024_bit_23_to_16,
  																										bit [7:0] DFIUPDTMG1_dfi_t_ctrlup_interval_max_x1024_bit_7_to_0,
  																										bit [9:0] DFIUPDTMG2_,
  																										bit [8:0] DFIUPDTMG3_dfi_t_ctrlupd_burst_interval_x8_bit_8_0); 
  				
    option.per_instance = 1;
    type_option.merge_instances = 0;
  
  	cp_OPCTRLCMD_ctrlupd : coverpoint OPCTRLCMD_ctrlupdp_bit_17 {
  	  option.comment = "This coverpoint covers both the values of field ctrlupd of Register OPCTRLCMD";
      bins cb_logic_1 = {1'b1} iff(DFIUPD0_dis_auto_ctrlupd_bit_31==1); // DFIUPDO.dis_auto_ctrlupd must be set to 1.
  		bins cb_logic_0 = {1'b0};
  	}
  
    cp_OPCTRLSTAT_ctlupd_busy : coverpoint OPCTRLSTAT_ctrlupd_busy_bit_16 {
  	  option.comment = "This coverpoint covers both the values of filed ctlupd_busy of Register OPCTRLDFIUPD0_dif_phyupd_en_bit_15STAT";
      bins cb_loigc_1 = {1'b1}; // ZQCS operation has not been initiated yet in DDRCTRL.
  		bins cb_logc_0  = {1'b0}; // SoC core can initiate a ZQCS operation. 
  	}
  
    cp_DFIUPD0_dfi_phyupd_en : coverpoint DFIUPD0_dif_phyupd_en_bit_15 {
  	  option.comment = "This coverpoint covers both the transition of field dif_phyupd_en of Register DFIUPD0";
      bins cb_logic_1 = (1'b0 => 1'b1);
  		bins cb_logic_0 = (1'b1 => 1'b0);
  	}
  
  	cp_DFITMG0_dfi_t_ctrl_delay : coverpoint DFITMG0_dfi_t_ctrl_delay_bit_28_to_24 {
  	  option.comment = "This coverpoint covers different values of field dfi_t_ctrl_delay of Regester DFITMG0";
      bins cb_comb_1 = {['h0:'h7]};   // with interval of 8
      bins cb_comb_2 = {['h8:'hf]};   // with interval of 8
      bins cb_comb_3 = {['h10:'h17]}; // with interval of 8
      bins cb_comb_4 = {['h18:'h1F]}; // with interval of 8
  	}
  
  	cp_DFIUPDTMG0_dif_t_ctrlup_min : coverpoint DFIUPDTMG0_dfi_t_ctrlup_min_bit_9_to_0 {
  	  option.comment = "This coverpoint covers different values of filed dfi_t_ctrlup_min of Register DFIUPDTMG0";
      bins cb_range_1 = {[10'h1:10'h100]};	 // interval of 255
  		bins cb_range_2 = {[10'h101:10'h200]}; // interval of 255
  		bins cb_range_3 = {[10'h201:10'h300]}; // interval of 255
  		bins cb_range_4 = {[10'h301:10'h400]}; // interval of 255	
  	}
  
  	cp_DFIUPDTMG0_dif_t_ctrlup_max : coverpoint DFIUPDTMG0_dfi_t_ctrlup_max_bit_25_to_16 {
  	  option.comment = "This coverpoint covers different values of filed dfi_t_ctrlup_max of Register DFIUPDTMG0";
      bins cb_range_1 = {[10'h1:10'h100]};	 // interval of 255
  		bins cb_range_2 = {[10'h101:10'h200]}; // interval of 255
  		bins cb_range_3 = {[10'h201:10'h300]}; // interval of 255
  		bins cb_range_4 = {[10'h301:10'h400]}; // interval of 255	
  	}
  
  	cp_DFIUPDTMG1_dfi_t_ctrlup_interval_min_x1024 : coverpoint DFIUPDTMG1_dfi_t_ctrlup_interval_min_x1024_bit_23_to_16 {
  	  option.comment = "This coverpoint covers different combinations of field dfi_t_ctrlupd_interval_min_x1024 of Register DFIUPDTMG1";
      bins cb_range_1 = {[8'h1:8'h3f]};      // interval of ~64	
      bins cb_range_2 = {[8'h40:8'h80]};     // interval of ~64
      bins cb_range_3 = {[8'h81:8'hC1]};     // interval of ~64
      bins cb_ragne_4 = {[8'hC2:8'hFF]};     // interval of ~64	 
  	}
  
  	cp_DFIUPDTMG1_dfi_t_ctrlup_interval_max_x1024 : coverpoint DFIUPDTMG1_dfi_t_ctrlup_interval_max_x1024_bit_7_to_0 {
  	  option.comment = "This coverpoint covers different combinations of field dfi_t_ctrlupd_interval_max_x1024 of Register DFIUPDTMG1";
      bins cb_range_1 = {[8'h1:8'h3f]};	     // interval of ~64
      bins cb_range_2 = {[8'h40:8'h80]};     // interval of ~64
      bins cb_range_3 = {[8'h81:8'hC1]};     // interval of ~64
      bins cb_ragne_4 = {[8'hC2:8'hFF]};	   // interval of ~64 	
  	}	
  
  	cp_DFIUPDTMG3_dfi_t_ctrlupd_burst_interval_x8 : coverpoint DFIUPDTMG3_dfi_t_ctrlupd_burst_interval_x8_bit_8_0 {
  	  option.comment = "This coverpoint covers different combinations of field dfi_t_ctrlupd_burst_interval_x8 of Register DFIUPDTMG3";
      bins cb_range_1 = {[9'd0:9'd127]};     // interval of 128
  		bins cb_range_2 = {[9'd128:9'd256]};   // interval of 128
  		bins cb_range_3 = {[9'd257:9'd385]};   // interval of 128
  		bins cb_range_4 = {[9'd386:9'd512]};   // interval of ~128
  	}
  endgroup:cg_dfi_updates_mode

endclass : lpddr5_subsystem_dfi_updates_covergroups
`endif // LPDDR5_SUBSYSTEM_DFI_UPDATES_COVERGROUPS
