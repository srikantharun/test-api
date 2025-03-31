// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_TEST_LIB_SVH
`define GUARD_TIMESTAMP_LOGGER_TEST_LIB_SVH

class timestamp_logger_test extends uvm_test;

  timestamp_logger_env_cfg m_env_cfg;
  timestamp_logger_env     m_env;
  rand int                 n_programs;
  rand int unsigned        random_cfg_read_rate;
  rand bit                 rate_limit;

  constraint c_n_programs           { soft n_programs           ==  1;   }
  constraint c_random_cfg_read_rate { soft random_cfg_read_rate == 0;    }
  constraint c_rate_limit           { soft rate_limit           == 1'b0; }

  `uvm_component_utils_begin(timestamp_logger_test)
    `uvm_field_int(n_programs,      UVM_DEFAULT)
  `uvm_component_utils_end

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    // Configure the env
    assert(this.randomize());
    m_env_cfg = timestamp_logger_env_cfg::type_id::create("m_env_cfg");
    assert(m_env_cfg.randomize() with {
                                        m_env_cfg.n_programs           == local::n_programs;
                                        m_env_cfg.random_cfg_read_rate == local::random_cfg_read_rate;
                                        m_env_cfg.rate_limit           == local::rate_limit;
    });
    uvm_config_db#(timestamp_logger_env_cfg)::set(this, "m_env", "m_env_cfg", this.m_env_cfg);

    m_env = timestamp_logger_env::type_id::create("m_env", this);
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

endclass : timestamp_logger_test

`include "timestamp_logger_internal_test_lib.svh"
`include "timestamp_logger_external_test_lib.svh"

`endif // GUARD_TIMESTAMP_LOGGER_TEST_LIB_SVH
