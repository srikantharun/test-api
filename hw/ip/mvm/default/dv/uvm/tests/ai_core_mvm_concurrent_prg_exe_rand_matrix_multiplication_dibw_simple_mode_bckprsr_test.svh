// MVM basic test-case class
`ifndef __AI_CORE_MVM_CONCURRENT_PRG_EXE_RAND_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_BACKPRSR_TEST__
`define __AI_CORE_MVM_CONCURRENT_PRG_EXE_RAND_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_BACKPRSR_TEST__

class ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_bckprsr_test extends ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_bckprsr_test)      
      bit prg_wt_set;
  // Class constructor
  function new (string name="ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_bckprsr_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_matrix_multiplication_base_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase); 
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_delay_sequence::type_id::get());

  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

      super.run_phase(phase);
      `uvm_info("MVM_CONCURRENT_PRG_EXE_RAND_MATRIX_MULT_DIBW_SIMPLE_TEST",$sformatf("MVM parallel random matrix multiplication with dibw simple mode starting"), UVM_LOW)
      `uvm_info("MVM_CONCURRENT_PRG_EXE_RANDOM_TEST",$sformatf("MVM parallel random matrix multiplication end"), UVM_LOW)
    phase.drop_objection(this);
  endtask



endclass:ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_bckprsr_test

`endif	// __AI_CORE_MVM_CONCURRENT_PRG_EXE_RANDOM_MATRIX_MULTIPLICATION_TEST__
