`ifndef GUARD_SOC_MGMT_BASE_TEST_SV
`define GUARD_SOC_MGMT_BASE_TEST_SV
// AI CORE soc_mgmt base test class
class soc_mgmt_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(soc_mgmt_base_test)
   // Declare p sequencer
  // `uvm_declare_p_sequencer(axi_virtual_sequencer)
  // soc_mgmt soc_mgmt RAL Modl
  soc_mgmt_reg_block soc_mgmt_regmodel;


  /** Instance of the environment */
  soc_mgmt_env env;

  /** Instance of the environment configuration */
  soc_mgmt_env_cfg m_env_cfg;

  /** Load through configCreator and load_prop_val */
  /** Required to set to 1 if load vip configurations through configCreator gui */
  bit load_through_config_creator = 0;

  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;

  /** Customized configCreator configuration handle */
  //cust_svt_axi_system_cc_configuration cc_cfg;
  uvm_status_e  status;
  // Semaphore
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  // soc_mgmt user Inteface Handle
  virtual soc_mgmt_if soc_mgmt_if;

  /** Class Constructor */
  function new(string name = "soc_mgmt_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(100ms,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);


    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)

    /** Create the configuration object */
    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");

    /** Set configuration in environment */
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    /** Create the configuration object for AI Core LS environment */
    m_env_cfg = soc_mgmt_env_cfg::type_id::create("m_env_cfg");
    /** Set configuration for AI Core soc_mgmt environment */
    uvm_config_db#(soc_mgmt_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    /** Create the environment */
    env = soc_mgmt_env::type_id::create("env", this);

    /** Apply the default sequence to the System ENV virtual sequencer
     * A virtual sequence is applied by default which generates unconstrained random
     * master transactions on all masters.  Extended tests can disable this behavior in
     * one of two ways:
     *   1) If using UVM 1.0 then this virtual sequence can be overriden with the
     *      axi_null_virtual_sequence.
     *   2) If using UVM 1.1 then his virtual sequence can be overriden by configuring
     *      the default sequence of the main phase as 'null'.
     *
     * Note that this sequence is configured using the uvm_object_wrapper with the
     * uvm_config_db. So extended tests must also configure the default_sequence using
     * the uvm_object_wrapper rather than using a sequence instance.
     */

    /** Apply the default reset sequence */
      uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    // random selection of slave response normal or zero delay sequence
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");

    // Recieve soc_mgmt user interface handle
    uvm_config_db#(virtual soc_mgmt_if)::get(
        uvm_root::get(), "uvm_test_top", "soc_mgmt_if", soc_mgmt_if);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  // Start of simulation phase
  function void start_of_simulation_phase (uvm_phase phase);
    uvm_config_db#(svt_axi_master_agent)::set(null,"*", "CFG_AXI_MST_AGENT", env.axi_system_env.master[0]);
  endfunction: start_of_simulation_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction: end_of_elaboration_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    soc_mgmt_regmodel = env.soc_mgmt_regmodel;
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
    
    `uvm_info("base_test:run_phase", "Entered...", UVM_LOW)
    
    `uvm_info("base_test:run_phase", "Exiting...", UVM_LOW)
  endtask

  /**
   * Calculate the pass or fail status for the test in the final phase method of the
   * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
   * test will fail.
   */
  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_LOW)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) +
        svr.get_severity_count(UVM_WARNING) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_NONE)
  endfunction: final_phase

endclass:soc_mgmt_base_test

`endif // GUARD_SOC_MGMT_BASE_TEST_SV
