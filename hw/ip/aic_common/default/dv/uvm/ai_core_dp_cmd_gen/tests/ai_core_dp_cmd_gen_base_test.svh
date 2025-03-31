// MVM basic test-case class
`ifndef GUARD_AI_CORE_DP_CMD_GEN_BASE_TEST
`define GUARD_AI_CORE_DP_CMD_GEN_BASE_TEST

class ai_core_dp_cmd_gen_base_test extends uvm_test;

  rand bit                   wait_on_done;
  rand int unsigned          rate;
  rand int                   n_agents;
  rand int                   n_programs;
  rand int                   n_transactions;
  rand int unsigned          pc_error;

  /** Instance of the environment configuration */
  ai_core_dp_cmd_gen_env_cfg m_env_cfg;

  ai_core_dp_cmd_gen_env     m_env;

  uvm_object_wrapper         legal_override_type   = null;
  uvm_object_wrapper         illegal_override_type = null;

  constraint c_cmdb_wait_on_done      { soft wait_on_done       == '0; }
  constraint c_cmdb_rate              { soft rate               == 100;}
  constraint c_cmdb_n_agents          { soft n_agents           ==  1; }
  constraint c_cmdb_n_programs        { soft n_programs         ==  1; }
  constraint c_cmdb_n_transacations   { soft n_transactions inside {[10:50]}; }
  constraint c_cmdb_pc_error          { soft pc_error           ==  0; }

  `uvm_component_utils_begin(ai_core_dp_cmd_gen_base_test)
    `uvm_field_int(wait_on_done,   UVM_DEFAULT)
    `uvm_field_int(rate,           UVM_DEFAULT)
    `uvm_field_int(n_agents,       UVM_DEFAULT)
    `uvm_field_int(n_programs,     UVM_DEFAULT)
    `uvm_field_int(n_transactions, UVM_DEFAULT)
    `uvm_field_int(pc_error,       UVM_DEFAULT)
  `uvm_component_utils_end

  function new (string name="ai_core_dp_cmd_gen_base_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);

    if (legal_override_type != null)
      set_type_override_by_type(ai_core_dp_cmd_gen_cmdb::get_type(),         legal_override_type,   1'b1);
    if (illegal_override_type != null)
      set_type_override_by_type(ai_core_dp_cmd_gen_cmdb_illegal::get_type(), illegal_override_type, 1'b1);

    // Configure the env
    // Add driver delay randomisation
    assert(this.randomize());
    m_env_cfg = ai_core_dp_cmd_gen_env_cfg::type_id::create("m_env_cfg");
    assert(m_env_cfg.randomize() with {
                                        m_env_cfg.cmdb_wait_on_done == local::wait_on_done;
                                        m_env_cfg.cmdb_rate         == local::rate;
                                        m_env_cfg.n_agents          == local::n_agents;
                                        m_env_cfg.n_programs        == local::n_programs;
                                        m_env_cfg.n_transactions    == local::n_transactions;
                                        m_env_cfg.cmdb_pc_error     == local::pc_error;
    });
    uvm_config_db#(ai_core_dp_cmd_gen_env_cfg)::set(this, "m_env", "m_env_cfg", this.m_env_cfg);
    m_env = ai_core_dp_cmd_gen_env::type_id::create("m_env", this);
  endfunction : build_phase

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
        svr.get_severity_count(UVM_ERROR)
	 > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
  endfunction: final_phase

endclass: ai_core_dp_cmd_gen_base_test

`endif	// GUARD_AI_CORE_DP_CMD_GEN_BASE_TEST
