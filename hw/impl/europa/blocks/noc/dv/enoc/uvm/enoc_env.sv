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
`ifndef GUARD_ENOC_ENV_SV
`define GUARD_ENOC_ENV_SV

class enoc_env extends uvm_env;

  `uvm_component_utils(enoc_env)

  /**environment configuration */
  enoc_env_cfg env_cfg;

  svt_axi_system_env  axi_system_env;
  svt_apb_system_env  apb_system_env[`NUM_APB3_TARGETS + `NUM_APB4_TARGETS];

  /** AXI System Configuration */
  cust_svt_axi_system_configuration axi_cfg;
  cust_svt_apb_system_configuration apb_cfg;

  /** Components */
  axi_virtual_sequencer sequencer; 
  //enoc_coverage                 enoc_cov;
  //enoc_scoreboard               enoc_scb;
  //cust_svt_axi_monitor_callback cb1;

  enoc_apb_targs_e enoc_targ;
  /** Class Constructor */
  function new(string name = "enoc_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (!uvm_config_db#(enoc_env_cfg)::get(this, "", "m_env_cfg", env_cfg))
      `uvm_fatal("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db")
  
    axi_cfg = cust_svt_axi_system_configuration::type_id::create("axi_cfg");
    uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", axi_cfg);
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);
    apb_cfg = new("apb_cfg"); 
    foreach (apb_system_env[i]) begin
      apb_system_env[i] = svt_apb_system_env::type_id::create($sformatf("apb_system_env_%s",enoc_targ.name()), this);
      uvm_config_db#(svt_apb_system_configuration)::set(this, $sformatf("apb_system_env_%s",enoc_targ.name()), "cfg", apb_cfg.apb_targ_cfg[i]);
      enoc_targ = enoc_targ.next();
    end

    //if (env_cfg.has_scoreboard) 
    //enoc_scb = enoc_scoreboard::type_id::create("enoc_scb", this);

    //if (env_cfg.has_coverage)
    //  enoc_cov = enoc_coverage::type_id::create("enoc_cov", this);
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    //if (env_cfg.has_scoreboard && !env_cfg.ral_test) begin
      /*****************************************************************************************/ 
      /** port connections from scoreboard to master monitors **/ 
      /*****************************************************************************************/ 
/*
      axi_system_env.master[init_ai_core_0_hp ].monitor.item_observed_port.connect (enoc_scb.aicore0_hp_reference_data_export );
      axi_system_env.master[init_ai_core_0_lp ].monitor.item_observed_port.connect (enoc_scb.aicore0_lp_reference_data_export );
      axi_system_env.master[init_ai_core_1_hp ].monitor.item_observed_port.connect (enoc_scb.aicore1_hp_reference_data_export );
      axi_system_env.master[init_ai_core_1_lp ].monitor.item_observed_port.connect (enoc_scb.aicore1_lp_reference_data_export );
      axi_system_env.master[init_ai_core_2_hp ].monitor.item_observed_port.connect (enoc_scb.aicore2_hp_reference_data_export );
      axi_system_env.master[init_ai_core_2_lp ].monitor.item_observed_port.connect (enoc_scb.aicore2_lp_reference_data_export );
      axi_system_env.master[init_ai_core_3_hp ].monitor.item_observed_port.connect (enoc_scb.aicore3_hp_reference_data_export );
      axi_system_env.master[init_ai_core_3_lp ].monitor.item_observed_port.connect (enoc_scb.aicore3_lp_reference_data_export );
      axi_system_env.master[init_pcie_hp      ].monitor.item_observed_port.connect (enoc_scb.pcie_hp_reference_data_export    );
      axi_system_env.master[init_sys_ctrl_lp  ].monitor.item_observed_port.connect (enoc_scb.sys_ctrl_lp_reference_data_export);
      axi_system_env.master[init_sys_dma_0_hp ].monitor.item_observed_port.connect (enoc_scb.sys_dma0_hp_reference_data_export);
      axi_system_env.master[init_sys_dma_1_hp ].monitor.item_observed_port.connect (enoc_scb.sys_dma1_hp_reference_data_export);
*/
      /*****************************************************************************************/ 
      /** port connections from scoreboard to slave monitors **/ 
      /*****************************************************************************************/
/*
      axi_system_env.slave[targ_ai_core_0_lp ].monitor.item_observed_port.connect (enoc_scb.aicore0_lp_actual_data_export   );
      axi_system_env.slave[targ_ai_core_1_lp ].monitor.item_observed_port.connect (enoc_scb.aicore1_lp_actual_data_export   );
      axi_system_env.slave[targ_ai_core_2_lp ].monitor.item_observed_port.connect (enoc_scb.aicore2_lp_actual_data_export   );
      axi_system_env.slave[targ_ai_core_3_lp ].monitor.item_observed_port.connect (enoc_scb.aicore3_lp_actual_data_export   );
      axi_system_env.slave[targ_l2_0_hp      ].monitor.item_observed_port.connect (enoc_scb.l2_0_hp_actual_data_export      );
      axi_system_env.slave[targ_l2_1_hp      ].monitor.item_observed_port.connect (enoc_scb.l2_1_hp_actual_data_export      );
      axi_system_env.slave[targ_l2_2_hp      ].monitor.item_observed_port.connect (enoc_scb.l2_2_hp_actual_data_export      );
      axi_system_env.slave[targ_l2_3_hp      ].monitor.item_observed_port.connect (enoc_scb.l2_3_hp_actual_data_export      );
      axi_system_env.slave[targ_pcie_dbi     ].monitor.item_observed_port.connect (enoc_scb.pcie_dbi_actual_data_export     );
      axi_system_env.slave[targ_pcie_lp      ].monitor.item_observed_port.connect (enoc_scb.pcie_lp_actual_data_export      );
      axi_system_env.slave[targ_ddrc_mp      ].monitor.item_observed_port.connect (enoc_scb.ddr_mp_actual_data_export       );
      axi_system_env.slave[targ_sys_ctrl_lp  ].monitor.item_observed_port.connect (enoc_scb.sys_ctrl_lp_actual_data_export  );

      apb_system_env[targ_ddrc_lp_v3].slave[0].monitor.item_observed_port.connect (enoc_scb.ddr_apb3_lp_actual_data_export  );
      apb_system_env[targ_ddrc_lp_v4].slave[0].monitor.item_observed_port.connect (enoc_scb.ddr_apb4_lp_actual_data_export  );
      apb_system_env[targ_pcie_cfg  ].slave[0].monitor.item_observed_port.connect (enoc_scb.pcie_cfg_apb4_actual_data_export);
    //end
*/
    `uvm_info("connect_phase", "Entered...",UVM_LOW)
     //cb1 = new("cust_svt_axi_monitor_callback_master");
     //foreach(axi_system_env.master[i]) begin
     // uvm_callbacks#(svt_axi_port_monitor, svt_axi_port_monitor_callback)::add(axi_system_env.master[i].monitor, cb1); 
     //end
/*
    if (env_cfg.has_coverage) begin
      axi_system_env.master[init_ai_core_0_hp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_0_hp ].analysis_export);
      axi_system_env.master[init_ai_core_0_lp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_0_lp ].analysis_export);
      axi_system_env.master[init_ai_core_1_hp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_1_hp ].analysis_export);
      axi_system_env.master[init_ai_core_1_lp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_1_lp ].analysis_export);
      axi_system_env.master[init_ai_core_2_hp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_2_hp ].analysis_export);
      axi_system_env.master[init_ai_core_2_lp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_2_lp ].analysis_export);
      axi_system_env.master[init_ai_core_3_hp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_3_hp ].analysis_export);
      axi_system_env.master[init_ai_core_3_lp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_ai_core_3_lp ].analysis_export);
      axi_system_env.master[init_pcie_hp      ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_pcie_hp      ].analysis_export);
      axi_system_env.master[init_sys_ctrl_lp  ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_sys_ctrl_lp  ].analysis_export);
      axi_system_env.master[init_sys_dma_0_hp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_sys_dma_0_hp ].analysis_export);
      axi_system_env.master[init_sys_dma_1_hp ].monitor.item_observed_port.connect (enoc_cov.taf_mon_init[init_sys_dma_1_hp ].analysis_export);
    end
*/
  endfunction : connect_phase

endclass : enoc_env

`endif  // GUARD_AI_CORE_TRITON_NOC_ENV_SV
