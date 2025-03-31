`ifndef GUARD_NOC_MEM_TEST_LIB
`define GUARD_NOC_MEM_TEST_LIB

class noc_mem_base_test extends uvm_test;

  noc_mem_env_cfg m_env_cfg;
  noc_mem_env     m_env;

  `uvm_component_utils(noc_mem_base_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

 function void build_phase(uvm_phase phase);
    m_env_cfg = noc_mem_env_cfg::type_id::create("m_env_cfg");
    assert(m_env_cfg.randomize());
    uvm_config_db#(noc_mem_env_cfg)::set(this, "m_env", "m_env_cfg", this.m_env_cfg);
    m_env = noc_mem_env::type_id::create("m_env", this);
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

endclass : noc_mem_base_test


class noc_mem_capacity_test extends noc_mem_base_test;

  `uvm_component_utils(noc_mem_capacity_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

 function void build_phase(uvm_phase phase);
    set_type_override_by_type(noc_mem_seq_base::get_type(), noc_mem_capacity_seq::get_type(), 1'b1);
    super.build_phase(phase);
  endfunction : build_phase
endclass : noc_mem_capacity_test

class noc_mem_random_test extends noc_mem_base_test;

  `uvm_component_utils(noc_mem_random_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

 function void build_phase(uvm_phase phase);
    set_type_override_by_type(noc_mem_seq_base::get_type(), noc_mem_random_seq::get_type(), 1'b1);
    m_env_cfg = noc_mem_env_cfg::type_id::create("m_env_cfg");
    assert(m_env_cfg.randomize() with {n_partitions == `DEPTH/8; });
    uvm_config_db#(noc_mem_env_cfg)::set(this, "m_env", "m_env_cfg", this.m_env_cfg);
    m_env = noc_mem_env::type_id::create("m_env", this);
  endfunction : build_phase
endclass : noc_mem_random_test

`endif // GUARD_NOC_MEM_TEST_LIB
