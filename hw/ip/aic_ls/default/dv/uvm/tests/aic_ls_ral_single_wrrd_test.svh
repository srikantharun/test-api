// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: RAL Test for single wr and read. Inherited
//              from Alpha.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_RAL_SINGLE_WRRD_TEST_SV
`define GUARD_AIC_LS_RAL_SINGLE_WRRD_TEST_SV

// Test to write/read, to/from one register for every CSR block of LS 
class aic_ls_ral_single_wrrd_test extends aic_ls_base_test;

  `uvm_component_utils (aic_ls_ral_single_wrrd_test);
  // Reset sequence
  axi_simple_reset_sequence m_axi_reset_seq;
  bit m_skip_reset = 0;

  // Single write/read sequence
  aic_ls_ral_access_single_wrrd_seq m_wrrd_seq;

  function new (string name="aic_ls_ral_single_wrrd_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);

    // Create simple reset sequence    
    m_axi_reset_seq = axi_simple_reset_sequence::type_id::create("m_axi_reset_seq");

    // Create the sequence class
    m_wrrd_seq = aic_ls_ral_access_single_wrrd_seq::type_id::create("m_wrrd_seq");

    `uvm_info(get_name(), "Exiting...", UVM_LOW)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);

    phase.raise_objection(this);
    `uvm_info(get_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)

    // Start reset sequence on the sequencer
    if (m_skip_reset==0) begin
      m_axi_reset_seq.start(m_env.m_axi_virt_sqr);
    end

    m_wrrd_seq.start(m_env.m_axi_virt_sqr);

    phase.drop_objection(this);
    `uvm_info(get_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)  
  endtask : run_phase
endclass:aic_ls_ral_single_wrrd_test
`endif
