// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Inherited test from Alpha. Does AXI
//   transactions to HP AXI interface to L1
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_AXI_DIRECTED_TEST_SV
`define GUARD_AIC_LS_AXI_DIRECTED_TEST_SV

// AI Core LS AXI directed test-case class
class aic_ls_axi_directed_test extends aic_ls_base_test;

  // Registration with the factory
  `uvm_component_utils(aic_ls_axi_directed_test)

  // Class Constructor
  function new(string name = "aic_ls_axi_directed_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build_phase", "Entered...", UVM_HIGH)
    super.build_phase(phase);

    // Apply the directed master sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.master[1].sequencer.main_phase",
                                            "default_sequence",
                                            axi_master_directed_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(
        this, "m_env.m_axi_system_env.master[1].sequencer.axi_master_directed_sequence",
        "sequence_length", 1000);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.slave[1].sequencer.run_phase",
                                            "default_sequence",
                                            axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("Build_phase", "Exiting...", UVM_HIGH)
  endfunction : build_phase
endclass:aic_ls_axi_directed_test

`endif // GUARD_AIC_LS_AXI_DIRECTED_TEST_SV
