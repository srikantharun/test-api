/**
 * Abstract:
 * This file creates a basetest, which serves as the base class for the rest
 * of the tests in this environment.  This test sets up the default behavior
 * for the rest of the tests in this environment.
 *
 * In the build_phase phase of the test we will set the necessary test related
 * information:
 *  - Use type wide factory override to set cust_svt_axi_master_transaction
 *    as the default master transaction type
 *  - Create a default configuration and set it to the l2_env instance
 *    using the configuration DB
 *  - Create the l2_env instance (named env)
 *  - Configure the axi_master_random_discrete_virtual_sequence as the default
 *    sequence for the main phase of the virtual sequence of the AXI System ENV
 *    virtual sequencer.  This sequence can be disabled by extended tests by
 *    setting the axi_null_virtual_sequence.
 *  - Configure the sequence length to 50
 *  - Configure the axi_slave_mem_response_sequence as the default
 *    sequence for all Slave Sequencers
 *  - Configure the axi_simple_reset_sequence as the default sequence
 *    for the reset phase of the TB ENV virtual sequencer
 */
`ifndef GUARD_L2_BASE_TEST_SV
`define GUARD_L2_BASE_TEST_SV
// L2 base test class
  //
`define L2_BASE_ADDR 'h0800_0000
class l2_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(l2_base_test)

  /** Instance of the environment */
  l2_env env;

  /** Instance of the environment configuration */
  l2_env_cfg env_cfg;

  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;

  apb_master_directed_sequence apb_dir_seq;
  cust_l2_svt_apb_system_cfg apb_cfg;
  virtual l2_power_if tb_cfg_if;

  warning_catcher catcher ;

  /** Class Constructor */
  function new(string name = "l2_base_test", uvm_component parent=null);
    super.new(name,parent);
    catcher = new();
  endfunction: new

  /**
   * Build Phase
   * - Create and apply the customized configuration transaction factory
   * - Create the TB ENV
   * - Set the default sequences
   */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    
    if ($test$plusargs("FORCE_FATAL_ERROR_TO_INFO"))
    begin
    uvm_report_cb::add(null, catcher);
    end

    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    // Loading configuration
    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)
    /** Create the configuration object */
    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");

    /** Set configuration in environment */
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    /** Create the configuration object for L2 environment */
    env_cfg = l2_env_cfg::type_id::create("env_cfg");

    /** Create the environment */
    env = l2_env::type_id::create("env", this);

    /** Set configuration for L2 environment */
    uvm_config_db#(l2_env_cfg)::set(this, "env", "env_cfg", this.env_cfg);

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
     if (!($test$plusargs("NO_DEFAULT_SEQ_RUN")) ) begin
    // uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.sequencer.main_phase", "default_sequence",     axi_master_random_discrete_virtual_sequence::type_id::get());

    /** Set the sequence 'length' to generate 5 transactions */
   // uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.sequencer.axi_master_random_discrete_virtual_sequence", "sequence_length", 5);
     end

    /** Apply the default reset sequence */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.apb_sequencer.reset_phase", "default_sequence", apb_simple_reset_sequence::type_id::get());
      


    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave[0].sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    apb_cfg = cust_l2_svt_apb_system_cfg::type_id::create("apb_cfg");
    uvm_config_db#(cust_l2_svt_apb_system_cfg)::set(this, "env.m_apb_system_env", "cfg", this.apb_cfg);
    apb_dir_seq = apb_master_directed_sequence::type_id::create("apb_dir_seq");
    uvm_config_db#(virtual l2_power_if)::get(uvm_root::get(), "", "tb_cfg_if", tb_cfg_if);


    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction: end_of_elaboration_phase

  
  virtual task post_reset_phase(uvm_phase phase);
    super.post_reset_phase(phase);
    `uvm_info(get_name(), "post_reset_phase() started.", UVM_LOW)
    phase.raise_objection(this);

    wait (tb_cfg_if.apb_rst == 0);
    repeat(3) @(posedge tb_cfg_if.ref_clk); // Make sure reset is synchronized
    `uvm_info(get_name(), "Out of reset", UVM_LOW)
    
    // only after setting reset address the reset can be removed:
    apb_dir_seq.cfg_addr        = 'h0000; // pctl_ao_csr_reg_ppmu_reset_control
    apb_dir_seq.cfg_data        = 'h1;
     // Start the sequence on the respective sequencer
    apb_dir_seq.start(env.m_apb_system_env.master.sequencer);

     `uvm_info(get_name(), "post_reset_phase() ended.", UVM_LOW)
    phase.drop_objection(this);
  endtask

  //Configure phase
  virtual task configure_phase(uvm_phase phase);
   phase.raise_objection(this);
    #500ns; //Every write should wait till the aicore rst is lifted
   phase.drop_objection(this);
  endtask : configure_phase

   //Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    #900ns;  // wait for the internal l2 internal reset  to lift and sync
    phase.drop_objection(this);
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
        svr.get_severity_count(UVM_WARNING) > 5000)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
  endfunction: final_phase


endclass

`endif // GUARD_L2_BASE_TEST_SV
