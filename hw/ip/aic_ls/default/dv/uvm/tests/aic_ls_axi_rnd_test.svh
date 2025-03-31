// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Inherited test from Alpha. Does AXI
//   transactions to HP AXI interface to L1 that generates
//   random transactions using built in SVT sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_AXI_RND_TEST_SV
`define GUARD_AIC_LS_AXI_RND_TEST_SV

// AI Core LS AXI random test-case class
class aic_ls_axi_rnd_test extends aic_ls_base_test;

  // Registration with the factory
  `uvm_component_utils(aic_ls_axi_rnd_test)

  // Class Constructor
  function new(string name = "aic_ls_axi_rnd_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_HIGH)
    super.build_phase(phase);

    // Apply the svt_axi_random_sequence
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.master[1].sequencer.main_phase",
                                            "default_sequence",
                                            svt_axi_master_random_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(
        this, "m_env.m_axi_system_env.master[1].sequencer.svt_axi_master_random_sequence",
        "sequence_length", 5000);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.slave[1].sequencer.run_phase",
                                            "default_sequence",
                                            axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("build_phase", "Exiting...", UVM_HIGH)
    m_init_l1_en = 1;
  endfunction : build_phase

endclass : aic_ls_axi_rnd_test
`endif

