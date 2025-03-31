// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_SQR_SVH
`define GUARD_NOC_MEM_SQR_SVH

class noc_mem_sqr extends uvm_sequencer#(noc_mem_item);

  noc_mem_env_cfg                  m_env_cfg;
  axe_uvm_memory_allocator         m_mem_allocator;

  `uvm_component_utils(noc_mem_sqr)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db#(axe_uvm_memory_allocator)::get(this, "", "m_mem_allocator", m_mem_allocator));
    assert(uvm_config_db#(noc_mem_env_cfg)::get(this,          "", "m_env_cfg",       m_env_cfg));
  endfunction : build_phase

endclass : noc_mem_sqr

`endif // GUARD_NOC_MEM_SQR_SVH
