
`ifndef LPDDR5_SUBSYSTEM_REFRESH_CONTROL_AND_MANAGEMENT_COVERGROUPS
`define LPDDR5_SUBSYSTEM_REFRESH_CONTROL_AND_MANAGEMENT_COVERGROUPS

/*class lpddr5_subsystem_refresh_control_and_management_covergroups extends uvm_component;

  //----------------------------------------------------------------------------
  // Register with factory
  //----------------------------------------------------------------------------
  `uvm_component_utils(lpddr5_subsystem_refresh_control_and_management_covergroups)

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments     : string name
  //                 uvm_component parent
  //----------------------------------------------------------------------------
  function new ( string name = "lpddr5_subsystem_refresh_control_and_management_covergroups", uvm_component parent = null);
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
  endfunction: connect_phase        */

  // Section Number : 4.1
  // Section Name   : Refresh Using Direct Software Request of Refresh Command
  
  //-----------------------------------------------------------------------------
  // Covergroup Name : cg_software_refresh_command
  // Arguments       : 1). per_bank_ref_cmd_gtr_63
  //                   2). all_bank_ref_cmd_gtr_9 
  // Description     : This covergroup covers coverage for section <Refresh Using
  //                   Direct Software Request of Refresh Command>
  //-----------------------------------------------------------------------------
  covergroup cg_software_refresh_command with function sample(bit RFSHCTL0_dis_auto_refresh_bit_0,
                                                              bit RFSHCTL0_refresh_update_level_bit_4,
                                                              //TODO : REMOVE bit [2:0] RFSHMOD1_fgr_mode,
                                                              bit OPREFCTRL0_rank0_refresh_bit_0,
                                                              bit OPREFCTRL0_rank1_refresh_bit_1,
                                                              //TODO :How to set bit per_bank_ref_cmd_gtr_63,
                                                              //TODO :Hpw to set bit all_bank_ref_cmd_gtr_9,
																											        bit RFSHMOD0_per_bank_refresh_bit_8,
																															bit OPREFSTAT0_rank0_refresh_busy_bit_0,
																															bit OPREFSTAT0_rank1_refresh_busy_bit_1);
    option.per_instance = 1;
    type_option.merge_instances=0; 
    cp_RFSHCTL0_dis_auto_refresh_bit_0 : coverpoint RFSHCTL0_dis_auto_refresh_bit_0 {
      option.comment = "This coverpoint covers both the value of field dis_auto_refresh of Register RFSHCTL0";
      bins cb_logic_1 = {1'b1};
      bins cb_logic_0 = {1'b0};
    }
  
    cp_OPREFCTRL0_rank0_refresh_bit_0 : coverpoint OPREFCTRL0_rank0_refresh_bit_0 {
      option.comment = "This coverpoint covers both the value of field rank0_refresh of Register OPREFCTRL0";
      bins cb_logic_1 = {1'b1};
      bins cb_logic_0 = {1'b0};
    }
  
    cp_OPREFCTRL0_rank0_refresh_bit_1 : coverpoint OPREFCTRL0_rank1_refresh_bit_1 {
      option.comment = "This coverpoint covers both the value of field rank1_refresh of Register OPREFCTRL0";
      bins cb_logic_1 = {1'b1};
      bins cb_logic_0 = {1'b0};
    }
  
    cp_RFSHMOD0_per_bank_refresh_bit_8 : coverpoint RFSHMOD0_per_bank_refresh_bit_8 {
      option.comment = "This coverpoint covers both the value of field per_bank_refresh of Register RFSHMOD0";
      bins cb_logic_1 = {1'b1};  // indicates Per bank refresh 
      bins cb_logic_0 = {1'b0};  // indicates All bank refresh
    }
  
    cp_OPREFSTAT0_rank0_refresh_busy_bit_0 : coverpoint OPREFSTAT0_rank0_refresh_busy_bit_0 {
      option.comment = "This coverpoint covers both the value of field rank0_refresh_busy of Register OPREFSTAT0";
      bins cb_logic_1 = {1'b1};
      bins cb_logic_0 = {1'b0};
    }
  
    cp_OPREFSTAT0_rank1_refresh_busy_bit_1 : coverpoint OPREFSTAT0_rank1_refresh_busy_bit_1 {
      option.comment = "This coverpoint covers both the value of field rank1_refresh_busy of Register OPREFSTAT0";
      bins cb_logic_1 = {1'b1};
      bins cb_logic_0 = {1'b0};
    }
  
    //cp_auto_refresh_per_bank : coverpoint {RFSHMOD0_per_bank_refresh_bit_8,per_bank_ref_cmd_gtr_63,all_bank_ref_cmd_gtr_9} {
    //  option.comment = "This coverpoint covers per bank refresh command is greater than 63 with both the value of dis_auto_refresh field of Register RFSHCTL0";
    //  bins cb_per_bank_ref_1_with_63_ref = {3'b110};
    //  bins cb_per_bank_ref_0_with_9_ref  = {3'b001};
    //}
  
    // if buffer saturates then 
    // Cover OPCTRLSTAT.rank*_refresh_busy == 1
  endgroup : cg_software_refresh_command
  
  // Section Number : 4.2
  // Section Name   : Per Bank Refresh Using Auto-Refresh Feature Test
  
  //-----------------------------------------------------------------------------
  // Covergroup  : cg_per_bank_refresh_using_auto_refresh_feature
  // Arguments   : 
  // Description : This covergroup is for test <Per Bank Refresh Using Auto-Refresh
  //               Feature Test> 
  //-----------------------------------------------------------------------------
  covergroup cg_per_bank_refresh_using_auto_refresh_feature with function sample(bit RFSHCTL0_dis_auto_refresh_bit_0,
                                                                                 bit RFSHMOD0_per_bank_refresh_bit_8,
                                                                                 bit RFSHCTL0_refresh_update_level_bit_4,
                                                                                 bit RFSHMOD0_auto_refab_en_bit_7_to_6,
                                                                                 bit FRSHMOD0_per_bank_refresh_opt_en_bit_9,
                                                                                 bit RFSHSET1TMG0_refresh_to_x1_sel_bit_30, 
                                                                                 bit RFSHSET1TMG0_t_refi_x1_sel_bit_31,
                                                                                 bit [5:0] RFSHMOD0_refresh_burst_bit_5_to_0);

    option.per_instance = 1;
    type_option.merge_instances = 0;
  
    cp_dis_auto_per_bank_refresh_update : coverpoint {RFSHCTL0_dis_auto_refresh_bit_0,RFSHMOD0_per_bank_refresh_bit_8,RFSHCTL0_refresh_update_level_bit_4} {
      option.comment = "This coverpoint cover logic 1 value of dis_auto_refresh , logic value of per_bank_refresh and toggle in refresh_update_level";
      bins cb_comb_1 = (3'b111 => 3'b110); // refresh_update_level 1 to 0
      bins cb_comb_2 = (3'b110 => 3'b111); // refresh_update_level 0 to 1
    }
  
    cp_RFSHMOD0_auto_refab_en : coverpoint RFSHMOD0_auto_refab_en_bit_7_to_6 {
      option.comment = "This coverpoint covers all possible the value of field auto_refab_en of Register RFSHMOD0";
      bins cb_comb_1 = {2'b00};
      bins cb_comb_2 = {2'b01};
      bins cb_comb_3 = {2'b10};
      bins cb_comb_4 = {2'b11};
    }
  
    cp_FRSHMOD0_per_bank_refresh_opt_en_bit_9 : coverpoint FRSHMOD0_per_bank_refresh_opt_en_bit_9 {
      option.comment = "This coverpoint covers both the value of field per_bank_refresh_opt_en of Regiset FRSHMOD0";
      bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
    }
  
    cp_RFSHSET1TMG0_refresh_to_x1_sel_bit_30 : coverpoint RFSHSET1TMG0_refresh_to_x1_sel_bit_30 {
      option.comment = "This coverpoint covers both the value of field refresh_to_x1 of Register RFSHSET1TMG0";
      bins cb_logic_0 = {1'b0}; // x32 register values are used
      bins cb_logic_1 = {1'b1}; // x1 register values are used
    }
  
    cp_RFSHSET1TMG0_t_refi_x1_sel_bit_31 : coverpoint RFSHSET1TMG0_t_refi_x1_sel_bit_31 {
      option.comment = "This coverpoint covers both the value of field t_refi_x1_sel of Register RFSHSET1TMG0";
      bins cb_logic_0 = {1'b0}; // x32 register values are used
      bins cb_logic_1 = {1'b1}; // x1 register values are used
    }
  
    cp_RFSHMOD0_refresh_burst_bit_5_to_0 : coverpoint RFSHMOD0_refresh_burst_bit_5_to_0 {
      option.comment = "This coverpoint covers different combinations of field refresh_burst of Register RFSHMOD0";
      bins cb_zero_valeu = {6'd0};           // single refresh
      bins cb_range_1    = {[6'd1: 6'd15]};  // interval of 2^6/4  
      bins cb_range_2    = {[6'd16:6'd31]};  // interval of 2^6/4 
      bins cb_range_3    = {[6'd32:6'd47]};  // interval of 2^6/4 
      bins cb_ragen_4    = {[6'd48:6'd63]};  // interval of 2^6/4  
    }
  endgroup : cg_per_bank_refresh_using_auto_refresh_feature
  
  // Section Number : 4.3
  // Section Name   : All Bank Refresh Using Auto-Refresh Feature Test
  
  //-----------------------------------------------------------------------------
  // covergroup  : cg_all_bank_refresh_using_auto_refresh
  // Arguments   : 
  // Description : This covergroup is for test <All Bank Refresh Using Auto-Refresh
  //               Feature Test>
  //-----------------------------------------------------------------------------
  covergroup cg_all_bank_refresh_using_auto_refresh with function sample(bit RFSHCTL0_dis_auto_refresh_bit_0,
                                                                         bit RFSHMOD0_per_bank_refresh_bit_8,
                                                                         bit RFSHCTL0_refresh_update_level_bit_4,
                                                                         bit [11:0] RFSHSET1TMG1_t_rfc_min_ab_bit_27_to_16,
                                                                         bit [5:0] RFSHSET1TMG3_refresh_to_ab_x32_bit_29_to_24,
                                                                         bit [5:0] RFSHMOD0_refresh_burst_bit_5_to_0
                                                                         );
    option.per_instance = 1;
    type_option.merge_instances = 0;
  
    cp_dis_auto_per_bank_refresh_update : coverpoint {RFSHCTL0_dis_auto_refresh_bit_0,RFSHMOD0_per_bank_refresh_bit_8,RFSHCTL0_refresh_update_level_bit_4} {
      option.comment = "This coverpoint cover logic 1 value of dis_auto_refresh , logic value of per_bank_refresh and toggle in refresh_update_level";
      bins cb_comb_1 = (3'b101 => 3'b100); // refresh_update_level 1 to 0
      bins cb_comb_2 = (3'b100 => 3'b101); // refresh_update_level 0 to 1
    }
  
    cp_RFSHSET1TMG1_t_rfc_min_ab_bit_27_to_16 : coverpoint RFSHSET1TMG1_t_rfc_min_ab_bit_27_to_16 {
      option.comment = "This coverpoint covers different combinations of field t_rfc_min_ab of Register RFSHSET1TMG1";
      bins cb_range_1 = {[12'd0: 12'd1023]};     // interval of 2^12/4 
      bins cb_range_2 = {[12'd1024 : 12'd2047]}; // interval of 2^12/4 
      bins cb_range_3 = {[12'd2048 : 12'd3072]}; // interval of 2^12/4 
      bins cb_range_4 = {[12'd3073 : 12'd4096]}; // interval of 2^12/4 
    }
    
    cp_RFSHSET1TMG3_refresh_to_ab_x32_bit_29_to_24 : coverpoint RFSHSET1TMG3_refresh_to_ab_x32_bit_29_to_24 {
      option.comment = "This coverpoint covers different combinations of field refresh_to_ab_x32 of Register RFSHSET1TMG3";
      bins cb_range_1 = {[6'd0: 6'd15]};  // interval of 2^6/4  
      bins cb_range_2 = {[6'd16:6'd31]};  // interval of 2^6/4 
      bins cb_range_3 = {[6'd32:6'd47]};  // interval of 2^6/4 
      bins cb_ragen_4 = {[6'd48:6'd63]};  // interval of 2^6/4  
    }
  
    cp_RFSHMOD0_refresh_burst_bit_5_to_0 : coverpoint RFSHMOD0_refresh_burst_bit_5_to_0 {
      option.comment = "This coverpoint covers different combinations of field refresh_burst of Register RFSHMOD0";
      bins cb_zero_valeu = {6'd0};           // single refresh
      bins cb_range_1    = {[6'd1: 6'd15]};  // interval of 2^6/4  
      bins cb_range_2    = {[6'd16:6'd31]};  // interval of 2^6/4 
      bins cb_range_3    = {[6'd32:6'd47]};  // interval of 2^6/4 
      bins cb_ragen_4    = {[6'd48:6'd63]};  // interval of 2^6/4  
    }
  
    cs_RFSHSET1TMG1_t_rfc_min_ab : cross cp_dis_auto_per_bank_refresh_update, cp_RFSHSET1TMG1_t_rfc_min_ab_bit_27_to_16 {
      option.comment = "This cross coverage covers different combinations of RFSHSET1TMG1.t_rfc_min_ab with logic 1 value of dis_auto_refresh , logic value of per_bank_refresh and toggle in refresh_update_level";
    }
  
    cs_RFSHSET1TMG3_refresh_to_ab_x32 : cross cp_dis_auto_per_bank_refresh_update, cp_RFSHSET1TMG3_refresh_to_ab_x32_bit_29_to_24 {
      option.comment = "This cross coverage covers different combinations of RFSHSET1TMG3.refresh_to_ab_x32 with logic 1 value of dis_auto_refresh , logic value of per_bank_refresh and toggle in refresh_update_level";
    }
  
    cs_RFSHMOD0_refresh_burst : cross cp_dis_auto_per_bank_refresh_update, cp_RFSHMOD0_refresh_burst_bit_5_to_0 {
      option.comment = "This cross coverage covers different combinations of RFSHMOD0.refresh_burst with logic 1 value of dis_auto_refresh , logic value of per_bank_refresh and toggle in refresh_update_level";
    }
  
  endgroup : cg_all_bank_refresh_using_auto_refresh
  
  // Section Number : 4.4
  // Section Name   : Automatic Temperature Derating Test
  
  //-----------------------------------------------------------------------------
  // Covergroup Name : cg_automatic_temp_derating_1
  // Argument        : 
  // Description     : This covergroup is for test <Automatic Temperature
  //                   Derating Test>.
  //-----------------------------------------------------------------------------
  covergroup cg_automatic_temp_derating_1 with function sample(bit DERATECTL0_derate_enable_bit_0,
                                                               bit DERATECTL6_derate_mr4_tuf_dis_bit_0,
                                                               bit [31:0] DERATEINT_mr4_read_interval_bit_31_to_0,
                                                               bit DERATECTL5_derate_temp_limit_intr_en_bit_0,
                                                               bit DERATECTL5_derate_temp_limit_intr_clr_bit_1, 
                                                               bit DERATECTL5_derate_temp_limit_intr_force_bit_2);
    option.per_instance = 1;
    type_option.merge_instances = 0;
  
    cp_DERATECTL0_derate_enable : coverpoint DERATECTL0_derate_enable_bit_0 {
      option.comment = "This coverpoint covers both the values of derate_enable of Register DERATECTL0";
      bins cb_logic_0 = {1'b0}; // Timing parameter de-rating is disabled
      bins cb_logic_1 = {1'b1}; // Timing parameter de-rating is enabled using MR4 read value.
    }
  
    cp_DERATECTL6_derate_mr4_tuf_dis_bit_0 : coverpoint DERATECTL6_derate_mr4_tuf_dis_bit_0 {
      option.comment = "This coverpoint covers both the values of derate_mr4_tuf_dis of Register DERATECTL0";
      bins cb_logic_0 = {1'b0}; 
      bins cb_logic_1 = {1'b1};
    }
  
    cp_DERATEINT_mr4_read_interval_bit_31_to_0 : coverpoint DERATEINT_mr4_read_interval_bit_31_to_0{
      option.comment = "This coverpoint covers different values of filed mr4_read_interval of Register DERATEINT";
      bins range_1 = {[32'd1:32'd1073741824]};          // interval of 2^32/4
      bins range_2 = {[32'd1073741825:32'd2147483648]}; // interval of 2^32/4
      bins range_3 = {[32'd2147483649:32'd3221225473]}; // interval of 2^32/4
      bins range_4 = {[32'd3221225474:32'd4294967296]}; // interval of 2^32/4
    }
  
    cp_DERATECTL5_derate_temp_limit_intr_en_bit_0 : coverpoint DERATECTL5_derate_temp_limit_intr_en_bit_0{
      option.comment = "This coverpoint covers both the value of field derate_temp_limit_intr_en of Register DERATECTL5";
      bins cb_logic_0 = {1'b0}; // Interrupt enable bit for derate_temp_limit_intr output pin : Disable
      bins cb_logic_1 = {1'b1}; // Interrupt enable bit for derate_temp_limit_intr output pin : Enable
    }
  
    // Memory Access : R/W1C
    cp_DERATECTL5_derate_temp_limit_intr_clr_bit_1 : coverpoint DERATECTL5_derate_temp_limit_intr_clr_bit_1 {
      option.comment = "This coverpoint covers both the value of field derate_temp_limit_intr_clr of Register DERATECTL5";
      bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
    }
  
    // Memory Access : R/W1C
    cp_DERATECTL5_derate_temp_limit_intr_force_bit_2 : coverpoint DERATECTL5_derate_temp_limit_intr_force_bit_2 {
      option.comment = "This coverpoint covers both the value of field derate_temp_limit_intr_force of Register DERATECTL5";
      bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
    }
  endgroup : cg_automatic_temp_derating_1
  
  
  //-----------------------------------------------------------------------------
  // Covergroup Name : cg_automatic_temp_derating_2
  // Argument        : 
  // Description     : This covergroup is for test <Automatic Temperature
  //                   Derating Test>.
  //-----------------------------------------------------------------------------
  covergroup cg_automatic_temp_derating_2 with function sample(bit DERATESTAT0_derate_temp_limit_intr_bit_0,
                                                               bit [1:0] derate_temp_limit_intr_fault,
                                                               bit [4:0] mr4_bit_4_to_0,
                                                               bit mr4_bit_7);
  
    option.per_instance = 1;
    type_option.merge_instances = 0;
    // Memory Access : Read Only
    cp_DERATESTAT0_derate_temp_limit_intr_bit_0 : coverpoint DERATESTAT0_derate_temp_limit_intr_bit_0 {
      option.comment = "This coverpoint covers both the value of field derate_temp_limit_intr of Register DERATESTAT0";
      bins cb_logic_0 = {1'b0}; //set to 0 by DERATECTL5.derate_temp_limit_intr_clr.
      bins cb_logic_1 = {1'b1}; //set to 1 when MR[4:0] is 5'b00000 or 5'b11111 or invalid value.
    }
  
    cp_derate_temp_limit_intr_fault : coverpoint derate_temp_limit_intr_fault {
      option.comment = "This coverpoint covers 2'b01 and 2'b10 value of output pin derate_temp_limit_intr_fault";
      bins cb_no_fault   = {2'b01}; // No Fault
      bins cb_with_fault = {2'b10}; // Fault Detected
      // OR transition fro No Fault to Fault and Fault to No Fault
      bins cb_no_fault_to_fault = (2'b01 => 2'b10);
      bins cb_fault_to_no_fault = (2'b10 => 2'b01);
    }
  
    cp_mr4_bit_4_to_0 : coverpoint mr4_bit_4_to_0  {
      option.comment = "This coverpoint covers different value of temperature in MR4[4:0]";
      bins cb_min_temp = {5'b00000};
      bins cb_max_temp = {5'b11111};
      bins cb_range_1  = {[5'd1:5'd8]};   // interval of 8
      bins cb_range_2  = {[5'd9:5'd16]};  // interval of 8
      bins cb_range_3  = {[5'd17:5'd24]}; // interval of 8
      bins cb_range_4  = {[5'd25:5'd30]}; // interval of ~8
    }
  
    cp_mr4_bit_7 : coverpoint mr4_bit_7 {
      option.comment = "This coverpoint covers both the value of bit 7 of MR4 command";
      bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
    }
  
  endgroup : cg_automatic_temp_derating_2
  
  // Section Number : 4.5
  // Section Name   : Refresh Management
  
  //-----------------------------------------------------------------------------
  // Covergroup Name : cg_refresh_management
  // Arguments       : RFMMOD0.rfm_en
  //                   RFMMOD0.rfmsbc
  // Description     : This covergoup is for test <Refresh Management> which
  //                   covers values of fields rfm_en and rfmsbc of register
  //                   RFMMOD0.
  //-----------------------------------------------------------------------------
  covergroup cg_refresh_management with function sample(bit RFMMOD0_rfm_en_bit_0,
                                                        bit RFMMOD0_rfmsbc_bit_4);
    option.per_instance = 1;
    type_option.merge_instances = 0;
  
    cp_RFMMOD0_rfm_en_bit_0 : coverpoint RFMMOD0_rfm_en_bit_0 {
      option.comment = "This coverpoint covers both the value of field rfm_em of Register RFMMOD0";
      bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
    }
  
    cp_RFMMOD0_rfmsbc_bit_4 : coverpoint RFMMOD0_rfmsbc_bit_4 {
      option.comment = "This coverpint covers both the value of field rfmsbc of Register RFMMOD0";
      bins cb_logic_0 = {1'b0};  // MR57:OP[5:4] == 2'b00 : One RAA Counter per two banks (1 of 8)
      bins cb_logic_1 = {1'b1};  // MR57:OP[5:4] == 2'b01 : One RAA counter per one bank (1 of 16)
    }
  endgroup : cg_refresh_management

//endclass : lpddr5_subsystem_refresh_control_and_management_covergroups

`endif // LPDDR5_SUBSYSTEM_REFRESH_CONTROL_AND_MANAGEMENT_COVERGROUPS
