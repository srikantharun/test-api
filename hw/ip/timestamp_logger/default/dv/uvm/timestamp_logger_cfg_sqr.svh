// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_CFG_SQR_SVH
`define GUARD_TIMESTAMP_LOGGER_CFG_SQR_SVH

class timestamp_logger_cfg_sqr extends uvm_sequencer#(timestamp_logger_cfg_item);

  timestamp_logger_env_cfg          m_env_cfg;

  `uvm_component_utils(timestamp_logger_cfg_sqr)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    assert(uvm_config_db#(timestamp_logger_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));
  endfunction : build_phase

endclass : timestamp_logger_cfg_sqr

`endif // GUARD_TIMESTAMP_LOGGER_CFG_SQR_SVH
