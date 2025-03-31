`ifndef GUARD_AI_CORE_LS_RAL_BASE_TEST_SV
`define GUARD_AI_CORE_LS_RAL_BASE_TEST_SV
// AI CORE LS base test class
class iau_ral_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_ral_base_test)

  /** Construct the report catcher extended class*/
  //warning_catcher catcher = new();

  /** Instance of the environment */
  iau_env env;

  /** Instance of the environment configuration */
  iau_env_cfg m_env_cfg;

  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;

  /** ICDF Enable bit*/
  bit icdf_enable; // 1-> enabled, 0-> disabled

  /** Class Constructor */
  function new(string name = "iau_ral_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(5ms,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    /** Add uvm_report_cb callback */
    //uvm_report_cb::add(null, catcher);

    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)

    /** Create the configuration object */
    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");

    /** Set configuration in environment */
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    /** Create the configuration object for AI Core LS environment */
    m_env_cfg = iau_env_cfg::type_id::create("m_env_cfg");
    if (!m_env_cfg.randomize()) `uvm_fatal(get_name, "Randomization Failed!")
    /** Set configuration for AI Core LS environment */
    uvm_config_db#(iau_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    /** Create the environment */
    env = iau_env::type_id::create("env", this);

    /** Apply the default reset sequence */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    // uvm_top.print_topology();
    super.end_of_elaboration_phase(phase);

    uvm_config_db#(bit)::set(null, "*", "ICDF_ENABLE", icdf_enable);
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction: end_of_elaboration_phase

  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_LOW)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) > 0)
        //svr.get_severity_count(UVM_WARNING) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
  endfunction: final_phase

endclass:iau_ral_base_test

`endif // GUARD_AI_CORE_LS_RAL_BASE_TEST_SV
