`ifndef GUARD_AI_CORE_DWPU_BASE_TEST_SV
`define GUARD_AI_CORE_DWPU_BASE_TEST_SV
// AI CORE DWPU base test class
class ai_core_dwpu_base_test extends uvm_test;
  bit RAL_TEST;
  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_dwpu_base_test)
  /** Variable that allows testcase to determine if the test pass/fail if there are uvm_warnings during the execution of it.
  * By default the value is 1, which means that if there is any uvm_warning during the test, then the test will fail */
  bit use_uvm_warn_on_pass_fail=1;
   // Declare p sequencer
  // `uvm_declare_p_sequencer(axi_virtual_sequencer)
  // AI Core DWPU RAL Modl
  dwpu_csr_reg_block regmodel;
  /** Construct the report catcher extended class*/
  warning_catcher catcher = new();
  `ifdef TARGET_GLS
    ai_core_dwpu_gls_demoter gls_demoter;
  `endif // TARGET_GLS
  /** Instance of the environment */
  ai_core_dwpu_env env;

  /** Instance of the environment configuration */
  ai_core_dwpu_env_cfg m_env_cfg;

  /** Customized configuration */
  dwpu_cust_svt_axi_system_configuration cfg;

  uvm_status_e  status;

  bit [AXI_LT_DATA_WIDTH-1:0] ral_write_data;
  bit [AXI_LT_DATA_WIDTH-1:0] ral_read_data;
  bit [AXI_LT_DATA_WIDTH-1:0] ral_read_prg_status;
  bit [AXI_LT_DATA_WIDTH-1:0] ral_read_exe_status;
  bit [AXI_LT_ADDR_WIDTH-1:0] axi_write_addr;
  bit [AXI_LT_DATA_WIDTH-1:0] axi_write_data;
  bit [AXI_LT_ADDR_WIDTH-1:0] axi_read_addr;
  bit [AXI_LT_DATA_WIDTH-1:0] axi_read_data;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  /** Class Constructor */
  function new(string name = "ai_core_dwpu_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(3ms,1);
    `ifdef TARGET_GLS
      gls_demoter = ai_core_dwpu_gls_demoter::type_id::create("gls_demoter");
    `endif // TARGET_GLS
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    if ($test$plusargs("RAL_TEST")) RAL_TEST = 1;
    /** Add uvm_report_cb callback */
    uvm_report_cb::add(null, catcher);

    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded dwpu_cust_svt_axi_system_configuration ", UVM_LOW)

    /** Create the configuration object */
    cfg = dwpu_cust_svt_axi_system_configuration::type_id::create("cfg");
    /** Call change_axi_cfg if necessary */
    change_axi_cfg();
    /** Set configuration in environment */
    uvm_config_db#(dwpu_cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    /** Create the configuration object for AI Core DWPU environment */
    m_env_cfg = ai_core_dwpu_env_cfg::type_id::create("m_env_cfg");
    m_env_cfg.ral_test = RAL_TEST;
    /** Set configuration for AI Core DWPU environment */
    uvm_config_db#(ai_core_dwpu_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    /** Create the environment */
    env = ai_core_dwpu_env::type_id::create("env", this);
    /** Apply the default reset sequence */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());

    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.m_axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    //uvm_top.print_topology(); //if needed please uncomment this line
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction: end_of_elaboration_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    regmodel = env.m_dwpu_regmodel;
  endfunction : connect_phase
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

    if (svr.get_severity_count(UVM_FATAL)
      + svr.get_severity_count(UVM_ERROR)
      //+ (svr.get_severity_count(UVM_WARNING) && use_uvm_warn_on_pass_fail) //TODO - remove this line when all warnings are fixed
        > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
  endfunction: final_phase

  virtual function void change_axi_cfg();
    //this should be overwritten on the extended testcases
  endfunction : change_axi_cfg

  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
    // set env in config db to be retrieved by non uvm components like report catcher and sequences
    uvm_config_db#(ai_core_dwpu_env_cfg)::set(null,"*", "AI_CORE_DWPU_ENV_CFG", env.env_cfg);
    `ifdef TARGET_GLS
      uvm_report_cb::add(null, gls_demoter); // only add after setting env cfg, else, it will FATAL error not getting the cfg at time 0
    `endif // TARGET_GLS
    `uvm_info("start_of_simulation_phase", "done", UVM_LOW)
  endfunction: start_of_simulation_phase

  virtual task reset_dwpu_env();
    -> env.dwpu_scb.m_rst_evt;
    @(posedge env.m_axi_system_env.vif.common_aclk);
    -> env.dwpu_scb.m_rst_done_evt;
    env.dwpu_mdl.reset();
  endtask
  
  task check_exec_done(int num_cycles=50);
    bit [63:0] read_data;
    uvm_status_e read_status;
    read_data = ~0;
    //wait program done by checking IDLE bit
    repeat(num_cycles) @(posedge env.m_axi_system_env.vif.common_aclk);
    //wait for idle = 1 : program is done
    while (|read_data[1:0]) begin // IDLE state == 0
      regmodel.cmdblk_status.read(read_status, read_data);
      repeat(100) @(posedge env.m_axi_system_env.vif.common_aclk);
    end
    `uvm_info ("check_exec_done", $sformatf("Program finished, DWPU in IDLE"), UVM_HIGH)
  endtask

endclass:ai_core_dwpu_base_test

`endif // GUARD_AI_CORE_DWPU_BASE_TEST_SV
