// ******************************************** //
// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //
// *****************************************************************************************
// Description: Class cust_svt_apb_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE

`ifndef GUARD_CUST_SVT_APB_SYSTEM_CONFIGURATION_SV
`define GUARD_CUST_SVT_APB_SYSTEM_CONFIGURATION_SV

class cust_svt_apb_system_configuration extends uvm_object;
  svt_apb_system_configuration apb_targ_cfg[`NUM_APB4_TARGETS + `NUM_APB3_TARGETS];

  enoc_apb_targs_e enoc_targ;
  // Factory registration
  `uvm_object_utils(cust_svt_apb_system_configuration)

  function new(string name = "cust_svt_apb_system_configuration");
    super.new(name);

    foreach(apb_targ_cfg[i]) begin
      apb_targ_cfg[i] = new($sformatf("apb_targ_cfg_%s",enoc_targ.name())); 
      enoc_targ = enoc_targ.next();
    end

    for(int f=e_lpddr_graph_0_targ_cfg; f < `NUM_APB3_TARGETS; f++ ) begin //{
      apb_targ_cfg[f].apb4_enable = 0;
      apb_targ_cfg[f].apb3_enable = 1;
    end //}

    for(int f=e_aic_0_targ_syscfg; f < (`NUM_APB3_TARGETS + `NUM_APB4_TARGETS); f++ ) begin //{
      apb_targ_cfg[f].apb4_enable = 1;
      apb_targ_cfg[f].apb3_enable = 1;
    end //}

    foreach (apb_targ_cfg[i]) begin //{
      if(i == e_dcd_targ_cfg || i == e_pcie_targ_cfg)
        apb_targ_cfg[i].paddr_width                                     = svt_apb_system_configuration::PADDR_WIDTH_20;
      else if((i == e_lpddr_graph_0_targ_cfg) || (i == e_lpddr_ppp_0_targ_cfg) ||
              (i == e_lpddr_graph_1_targ_cfg) || (i == e_lpddr_ppp_1_targ_cfg) ||
              (i == e_lpddr_graph_2_targ_cfg) || (i == e_lpddr_ppp_2_targ_cfg) ||
              (i == e_lpddr_graph_3_targ_cfg) || (i == e_lpddr_ppp_3_targ_cfg) )
        apb_targ_cfg[i].paddr_width                                     = svt_apb_system_configuration::PADDR_WIDTH_32;
      else
        apb_targ_cfg[i].paddr_width                                     = svt_apb_system_configuration::PADDR_WIDTH_16;
      apb_targ_cfg[i].pdata_width                                       = svt_apb_system_configuration::PDATA_WIDTH_32;
      apb_targ_cfg[i].num_slaves                                        = 1;
      apb_targ_cfg[i].disable_x_check_of_pclk                           = 1; //TODO: en after sim
      apb_targ_cfg[i].disable_x_check_of_presetn                        = 1; //TODO: en after sim
      apb_targ_cfg[i].is_active                                         = 1;
      apb_targ_cfg[i].enable_xml_gen                                    = 0;
      apb_targ_cfg[i].transaction_coverage_enable                       = 1;
      apb_targ_cfg[i].protocol_checks_coverage_enable                   = 1;
      apb_targ_cfg[i].trace_enable                                      = 0;
      apb_targ_cfg[i].reasonable_constraint_mode ( 1'b1 );

      apb_targ_cfg[i].create_sub_cfgs(1);
      apb_targ_cfg[i].slave_cfg[0].enable_xml_gen                       = 0;
      apb_targ_cfg[i].slave_cfg[0].is_active                            = 1;
      apb_targ_cfg[i].slave_cfg[0].slave_id                             = 0;
      apb_targ_cfg[i].slave_cfg[0].transaction_coverage_enable          = 1;
      apb_targ_cfg[i].slave_cfg[0].protocol_checks_coverage_enable      = 1;
      apb_targ_cfg[i].slave_cfg[0].trace_enable                         = 0;
      apb_targ_cfg[i].slave_cfg[0].default_pready                       = 1;
      apb_targ_cfg[i].slave_cfg[0].reasonable_constraint_mode ( 1'b1 );
    end //}

  endfunction : new 

endclass
`endif  //GUARD_CUST_SVT_APB_SYSTEM_CONFIGURATION_SV
