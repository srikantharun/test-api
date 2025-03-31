`ifndef LPDDR5_SUBSYSTEM_PERIODIC_MEMORY_AND_PHY_MAINTENANCE_COVERGROUPS
`define LPDDR5_SUBSYSTEM_PERIODIC_MEMORY_AND_PHY_MAINTENANCE_COVERGROUPS

class lpddr5_subsystem_periodic_memory_and_phy_maintenance_covergroups extends uvm_component;

  //----------------------------------------------------------------------------
  // Register with factory
  //----------------------------------------------------------------------------
  `uvm_component_utils(lpddr5_subsystem_periodic_memory_and_phy_maintenance_covergroups)

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments     : string name
  //                 uvm_component parent
  //----------------------------------------------------------------------------
  function new ( string name = "lpddr5_subsystem_periodic_memory_and_phy_maintenance_covergroups", uvm_component parent = null);
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
  
	parameter REGISTER_WIDTH = 32;

  // Section Number : 5.1
  // Section Name   : ZQ Calibration Test
  
  //-----------------------------------------------------------------------------
  // Covergroup  : cg_zq_calibration
  // Arguments   : ZQCTL0, ZQCTL1, ZQSTAT, ZQTMG0,
  //               ZQSET1MG1, ZQCTL2 Registers
  // Description : This covergroup is for test case <ZQ Calibration Test>.
  //-----------------------------------------------------------------------------
  covergroup cg_zq_calibration with function sample(bit [REGISTER_WIDTH-1:0] ZQCTL0, 
  				                                                                   ZQCTL1, 
  																														               ZQSTAT, 
  																														               ZQTMG0, 
  																														               ZQSET1MG1, 
  																														               ZQCTL2,
                                                                             ZQSET1TMG0,
																																						 ZQSET1TMG1,
																																						 ZQSET1MG2,
																										bit ZQCTL2_dis_srx_zqcl_bit_,
																	                  bit perf_precharge_for_other,
																	                  bit perf_op_is_zqstart,									
																										bit perf_op_is_zqlatch,
																										bit sr_power_down_exit);
  
    option.per_instance = 1;
    type_option.merge_instances = 0; 
  	cp_ZQCTL0_dis_auto_zq : coverpoint ZQCTL0[31] {
  	  option.comment = "This coverpoint covers both the transition of field dis_auto_zq of Register ZQCTL0";
      bins cb_trans_to_1 = (1'b0 => 1'b1);
  		bins cb_trans_to_0 = (1'b1 => 1'b0);
  	}
  
  	cp_ZQCTL1_zq_reset : coverpoint ZQCTL1[0] {
  	  option.comment = "This coverpoint covers both the value of field zq_reset of Register ZQCTL1";
      bins cb_trans_to_1 = (1'b0 => 1'b1);  // Not to set this bit in SR-Powerdown and 
                                            // Deep Sleep Modes
  		bins cb_trans_to_0 = (1'b1 => 1'b0);
  	}
  
  	cp_ZQSTAT_zq_reset_busy : coverpoint ZQSTAT[0] {
  	  option.comment = "This coverpoint covers both the value of zq_reset_busy field of Register ZQSTAT";   
  		bins cb_logic_1   = {1'b1};
  		bins cb_logic_0   = {1'b0};
  	}
  
  	cp_different_values_of_ZQSET1TMG0 : coverpoint ZQSET1TMG0[25:16] {
      option.comment = "This coverpiont covers different combinations of fields t_zq_short_nop of Registers ZQSET1TMG0";
      bins cb_range_1 = {[10'h1:10'h100]};	 // interval of 255
  		bins cb_range_2 = {[10'h101:10'h200]}; // interval of 255
  		bins cb_range_3 = {[10'h201:10'h300]}; // interval of 255
  		bins cb_range_4 = {[10'h301:10'h400]}; // interval of 255
  	}
  
  	cp_ZQSET1TMG1_t_zq_reset_nop : coverpoint ZQSET1TMG1[29:20]{
  	  option.comment = "This coverpoint covers different combinations of field t_zq_reset_nop of Register ZQSET1TMG1";
      bins cb_range_1 = {[10'h1:10'h100]};	 // interval of 255
  		bins cb_range_2 = {[10'h101:10'h200]}; // interval of 255
  		bins cb_range_3 = {[10'h201:10'h300]}; // interval of 255
  		bins cb_range_4 = {[10'h301:10'h400]}; // interval of 255
  	}
  
  	cp_ZQSET1TMG2_t_zq_stop : coverpoint ZQSET1MG2[6:0] {
  	  option.comment = "This coverpoint covers different combinations of field t_zq_stop of Register ZQSET1TMG2";
      bins cb_range_1 = {[10'h1:10'h100]};	 // interval of 255
  		bins cb_range_2 = {[10'h101:10'h200]}; // interval of 255
  		bins cb_range_3 = {[10'h201:10'h300]}; // interval of 255
  		bins cb_range_4 = {[10'h301:10'h400]}; // interval of 255
  	}
  
  	cp_ZQSET1TMG1_t_zq_short_interval_x1024 : coverpoint ZQSET1MG1[19:0] { //TODO Need to add iff(ZQCTL0.dis_auto_zq==0) condition
  	  option.comment = "This coverpoint covers different combinations of field t_zq_short_interval_x1024 of Register ZQSET1MG1";
      bins cb_range_1 = {[20'd1:20'd262144]};       // interval of 262144
      bins cb_range_2 = {[20'd262145:20'd524288]};  // interval of 262144 
  	  bins cb_range_3 = {[20'd524289:20'd786432]};  // interval of 262144
  	  bins cb_range_4 = {[20'd786433:20'd1048576]}; // interval of 262144	
    }
  
  	cp_ZQCTL2_dis_srx_zqcl : coverpoint ZQCTL2_dis_srx_zqcl_bit_ {
  	  option.comment = "This coverpoint covers both the value of field dis_srz_zqcl of Register ZQCTL2 with SR-Power Down Exit";
      bins cb_logic_1 = {1'b1} iff(sr_power_down_exit==1); // cover logic 1 with SR-Power Down Exit
  		bins cb_logic_0 = {1'b0} iff(sr_power_down_exit==1); // cover logic 0 with SR-Power Down Exit
  	}
  
  	cp_perf_precharge_for_other_due_to_zq_calib : coverpoint perf_precharge_for_other {
  	  option.comment = "This coverpoint covers logic 1 value of perf_precharge_for_other signal due to ZQ Calib";
  	  bins cb_logic_1 = {1'b1};// iff(CMD==ZQ_CALIB); TODO : Need to provide command equal to ZQ_CALIB
  	}
  
  	cp_perf_op_is_zqstart_due_to_zq_calib : coverpoint perf_op_is_zqstart {
  	  option.comment = "This coverpoint covers logic 1 value of output signal perf_op_is_zqstart due to ZQ Calib";
      bins cb_logic_1 = {1'b1}; //iff(CMD==ZQ_CALIB); TODO : Need to provide command equal to ZQ_CALIB
  	}
  
  	cp_perf_op_is_zqlatch_due_to_zq_calib : coverpoint perf_op_is_zqlatch {
  	  option.comment = "This coverpoint covers logic 1 value of output signal perf_op_is_zqlatch due to ZQ_Calib";
      bins cb_logic_1 = {1'b1};// iff(CMD==ZQ_CALIB); TODO : Need to provide command equal to ZQ_CALIB
  	}
  endgroup: cg_zq_calibration
  
  // Section Number : 5.2
  // Section Name   : MRR Snooping Test
  
  //-----------------------------------------------------------------------------
  // Coverage Name  :  cg_mrr_snooping
  // Arguments      :  Register DQSOSCRUNTIME and DQSOSCCTL0
  // Description    :  This covergroup is for test case <MRR Snooping Test> in 
  //                   Which we are covering different values of dqsosc_runtime
  //                   of Register DQSOSCRUNTIME. 
  //-----------------------------------------------------------------------------
  covergroup cg_mrr_snooping with function sample(bit [REGISTER_WIDTH-1:0] DQSOSCRUNTIME, DQSOSCCTL0,
	                                                bit perf_op_is_dqsosc_mpc,
																									bit perf_op_is_dqsosc_mrr,
                                                  bit perf_precharge_for_other,
																									bit perf_op_is_tcr_mr);
    option.per_instance = 1;
    type_option.merge_instances = 0; 
  
  	//--------------------------------------------------------------------------
  	// Coverage for DQSOSCRUNTIME
  	//--------------------------------------------------------------------------
    cp_DQSOSCRUNTIME_wck2dqo_runtim : coverpoint DQSOSCRUNTIME[23:16] {
      option.comment = "This coverpoint covers different values of filed wck2dqo of Register DQSOSCRUNTIME";
      bins cb_range_1  = {['h1:'h8]};   // with interval of 8
      bins cb_range_2  = {['h9:'h11]};  // with interval of 8 
      bins cb_range_3  = {['h12:'h19]}; // with interval of 8
      bins cb_range_4  = {['h1A:'h22]}; // with interval of 8
      bins cb_range_5  = {['h23:'h2B]}; // with interval of 8
      bins cb_range_6  = {['h2C:'h34]}; // with interval of 8
      bins cb_range_7  = {['h35:'h3D]}; // with interval of 8
      bins cb_range_8  = {['h3E:'h3F]}; // with interval of 2
      bins cb_range_9  = {['h40:'h7F]}; // interval timer stops automatically at 2048 th clocks after timer starts
      bins cb_range_10 = {['h80:'hBF]}; // interval timer stops automatically at 4096 th clocks after timer starts
      bins cb_range_11 = {['hC0:'hFF]}; // interval timer stops automatically at 2048 th clocks after timer starts
      // Note : 0 indicates interval time stop via MPC command and is not supported
    }
  	
    cp_DQSOSCRUNTIME_dqsosc_runtime : coverpoint DQSOSCRUNTIME[7:0] {
      option.comment = "This coverpoint covers different values of filed wck2dqo of Register DQSOSCRUNTIME";
      bins cb_range_1  = {['h1:'h8]};   // with interval of 8
      bins cb_range_2  = {['h9:'h11]};  // with interval of 8 
      bins cb_range_3  = {['h12:'h19]}; // with interval of 8
      bins cg_range_4  = {['h1A:'h22]}; // with interval of 8
      bins cb_range_5  = {['h23:'h2B]}; // with interval of 8
      bins cb_range_6  = {['h2C:'h34]}; // with interval of 8
      bins cb_range_7  = {['h35:'h3D]}; // with interval of 8
      bins cb_range_8  = {['h3E:'h3F]}; // with interval of 2
      bins cb_range_9  = {['h40:'h7F]}; // interval timer stops automatically at 2048 th clocks after timer starts
      bins cb_range_10 = {['h80:'hBF]}; // interval timer stops automatically at 4096 th clocks after timer starts
      bins cb_range_11 = {['hC0:'hFF]}; // interval timer stops automatically at 2048 th clocks after timer starts
      // Note : 0 indicates interval time stop via MPC command and is not supported   
    }
  
    //---------------------------------------------------------------------------
    // Coverage for DQSOSCCTL0 Register
    //---------------------------------------------------------------------------
    cp_DQSOSCCTL0_dqsosc_enable : coverpoint DQSOSCCTL0[0] {
      option.comment = "This coverpoint covers both the transition of field dqsosc_enable of Register DQSOSCCTL0";
      bins cb_trans_0_to_1 = (1'b0 => 1'b1); // Enable DQS Oscillator
      bins cb_trans_1_to_0 = (1'b1 => 1'b0); // Disable DQS Oscillator
    }
  
    cp_DQSOSCCTL0_dqsosc_interval : coverpoint DQSOSCCTL0[15:4] {
      option.comment = "This coverpoint covers different ranges of field dqsosc_interval of Register DQSOSCCTL0 when DQSOSCCTL0.dqsosc_enable is 0";
      bins cb_range_1 = {['h1:'h1FF]}   iff(DQSOSCCTL0[0]==0); // interval of 511
      bins cb_range_2 = {['h200:'h3FF]} iff(DQSOSCCTL0[0]==0); // interval of 511 
      bins cb_range_3 = {['h400:'h5FF]} iff(DQSOSCCTL0[0]==0); // interval of 511
      bins cb_range_4 = {['h600:'h7FF]} iff(DQSOSCCTL0[0]==0); // interval of 511
      bins cb_range_5 = {['h800:'h9FF]} iff(DQSOSCCTL0[0]==0); // interval of 511
      bins cb_range_6 = {['hA00:'hBFF]} iff(DQSOSCCTL0[0]==0); // interval of 511
      bins cb_range_7 = {['hC00:'hDFF]} iff(DQSOSCCTL0[0]==0); // interval of 511
      bins cb_range_8 = {['hE00:'hFFF]} iff(DQSOSCCTL0[0]==0); // interval of 511
      // Note minimum programmable value is 1.
    }
  
    cp_DQSOSCCTL0_dqsosc_interval_unit : coverpoint DQSOSCCTL0[2] {
      option.comment = "This coverpoint covers both the value of field dqsosc_interval_unit of Register DQSOSCCTL0 when DQSOSCCTL0.dqsosc_enable is 0";
      bins cb_logic_1 = {'b1} iff(DQSOSCCTL0[0]==0); // x2K DFI clock cycles
      bins cb_logic_0 = {'b0} iff(DQSOSCCTL0[0]==0); // x32K DFI clock cycles
    }
  
    cross_dqsosc_interval_with_dqsosc_interval_unit : cross cp_DQSOSCCTL0_dqsosc_interval, cp_DQSOSCCTL0_dqsosc_interval_unit {
      option.comment = "This cross coverage covers all possible value between dqsosc_interval and dqsosc_interval_unit";
    }
  
  	cp_perf_op_is_dqsosc_mpc : coverpoint perf_op_is_dqsosc_mpc {
  	  option.comment = "This coverpoint covers both the values of output signal perf_op_is_dqsosc_mpc";
      bins cb_logic_1 = {1'b1};
  		bins cb_logic_0 = {1'b0};
  	}
  
  	cp_perf_op_is_dqsosc_mrr : coverpoint perf_op_is_dqsosc_mrr {
  	  option.comment = "This coverpoint covers both the value of output signal perf_op_is_dqsosc_mrr";
      bins cb_logic_1 = {1'b1};
  		bins cb_logic_0 = {1'b0};
  	}
  
  	cp_perf_precharge_for_other_due_to_mrr : coverpoint perf_precharge_for_other {
  	  option.comment = "This coverpoint covers that output signal perf_precharge_for_other is set to 1 due to MRR Command";
      bins cb_set_to_1 = (1'b0 => 1'b1);// iff(PRE_CMD==MRR); TODO: Need to add command equal to MRR
  	}
  
  	cp_perf_op_is_tcr_mr_due_to_mrr : coverpoint perf_op_is_tcr_mr {
  	  option.comment = "This coverpoint covers that output signal perf_op_is_tcr_mr is set to 1 due to MRR Command";
      bins cb_set_to_1 = (1'b0 => 1'b1);// iff(PRE_CMD==MRR); TODO : Need to add command equal to MRR
  	}
  endgroup: cg_mrr_snooping

endclass : lpddr5_subsystem_periodic_memory_and_phy_maintenance_covergroups

`endif // LPDDR5_SUBSYSTEM_PERIODIC_MEMORY_AND_PHY_MAINTENANCE_COVERGROUPS
