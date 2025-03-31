`ifndef GUARD_AI_CORE_MVM_RAL_BASE_TEST_SV
`define GUARD_AI_CORE_MVM_RAL_BASE_TEST_SV

// AI CORE MVM base test class
class ai_core_mvm_ral_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_mvm_ral_base_test)

  /** Construct the report catcher extended class*/
  ai_core_mvm_demoter catcher = new();

  /** Instance of the environment */
  ai_core_mvm_env env;

  /** Instance of the environment configuration */
  ai_core_mvm_env_cfg m_env_cfg;

  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;
   // MVM user define interface
  virtual mvm_if mvm_if;

  /** Class Constructor */
  function new(string name = "ai_core_mvm_ral_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(5ms,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_HIGH)
    super.build_phase(phase);

    /** Add uvm_report_cb callback */
    uvm_report_cb::add(null, catcher);

    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_HIGH)

    /** Create the configuration object */
    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");

    /** Set configuration in environment */
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    /** Create the configuration object for AI Core LS environment */
    m_env_cfg = ai_core_mvm_env_cfg::type_id::create("m_env_cfg");
    /** Set configuration for AI Core LS environment */
    uvm_config_db#(ai_core_mvm_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    /** Create the environment */
    env = ai_core_mvm_env::type_id::create("env", this);

    /** Apply the default reset sequence */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
    uvm_config_db#(virtual mvm_if)::get(uvm_root::get(), "", "mvm_if", mvm_if);
    `uvm_info("build_phase", "Exiting...", UVM_HIGH)
  endfunction: build_phase

  // Start of simulation phase
  function void start_of_simulation_phase (uvm_phase phase);
    // set cfg axi mst agent in config db to be retrieved by non uvm components like report catcher
    uvm_config_db#(svt_axi_master_agent)::set(null,"*", "CFG_AXI_MST_AGENT", env.axi_system_env.master[0]);
  endfunction: start_of_simulation_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_HIGH)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_HIGH)
  endfunction: end_of_elaboration_phase

  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_HIGH)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) > 0)
        //svr.get_severity_count(UVM_WARNING) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_NONE)
  endfunction: final_phase

endclass:ai_core_mvm_ral_base_test

`endif // GUARD_AI_CORE_MVM_RAL_BASE_TEST_SV
