// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: RAL Test on all registers.
// Owner: Jorge Carvalho <jorge.carvalho@axelera.ai>

`ifndef GUARD_AI_CORE_DWPU_RAL_TEST_SV
`define GUARD_AI_CORE_DWPU_RAL_TEST_SV

/** AI Core DWPU registers write/read testcase class
* This testcase does the verification of status and data of registers that do not have RO fields.
* There are three sequences from built in RAL sequences that are ran: hw_reset, bit_bash and reg_access.
*/
class ai_core_dwpu_ral_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_ral_test);
  uvm_reg_mem_built_in_seq m_ral_seq;

  function new (string name="ai_core_dwpu_ral_test", uvm_component parent);
    super.new (name, parent);
    //is this test, is expected to have uvm_warnings triggered by the uvm_reg_access_seq when accessing bits that are RO
    use_uvm_warn_on_pass_fail=0;
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    set_type_override_by_type(svt_axi_reg_adapter::get_type(), ai_core_dwpu_axi_slverr_adapter::get_type());
    super.build_phase(phase);
    `uvm_info(get_name(), "is entered", UVM_LOW)
    m_ral_seq = uvm_reg_mem_built_in_seq::type_id::create("m_ral_seq",,get_full_name());

    `uvm_info(get_name(), "build - is exited", UVM_LOW)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    phase.get_objection().set_drain_time(this, 150);
    phase.raise_objection(this);
    // =======================================================================================================================
    // DWPU RAL model
    // =======================================================================================================================
    m_ral_seq.model = regmodel;
    // Call start method to start built-in sequences.
    `uvm_info(get_name(), "Before sequence start", UVM_LOW)
    m_ral_seq.tests = (UVM_DO_REG_HW_RESET | UVM_DO_REG_BIT_BASH | UVM_DO_REG_ACCESS);
    m_ral_seq.start(null);
    `uvm_info(get_name(), "After sequence start", UVM_LOW)
    regmodel.print();
    `uvm_info(get_name(), "Run phase exited", UVM_LOW)
    phase.drop_objection(this);
  endtask : run_phase
endclass:ai_core_dwpu_ral_test
`endif // GUARD_AI_CORE_DWPU_RAL_TEST_SV
