// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Testcase to check the LP DMA access from SYS SPM to SPM memory
// Owner: Roswin Benny <roswin.benny@axelera.ai>
`ifndef __AI_CORE_LP_DMA_SYSSPM_TO_SPM_TEST__
`define __AI_CORE_LP_DMA_SYSSPM_TO_SPM_TEST__

class ai_core_lp_dma_sysspm_to_spm_test extends ai_core_dma_base_test;

  // Class constructor
  extern function new (string name = "ai_core_lp_dma_sysspm_to_spm_test", uvm_component parent);

  // Build phase
  extern virtual function void build_phase(uvm_phase phase);

  // Run phase
  extern virtual task main_phase(uvm_phase phase);

  // Registration with the factory
  `uvm_component_utils(ai_core_lp_dma_sysspm_to_spm_test)

endclass : ai_core_lp_dma_sysspm_to_spm_test

function ai_core_lp_dma_sysspm_to_spm_test::new (string name="ai_core_lp_dma_sysspm_to_spm_test", uvm_component parent);
  super.new (name, parent);
endfunction : new

function void ai_core_lp_dma_sysspm_to_spm_test::build_phase(uvm_phase phase);
  `uvm_info (get_type_name(), "Build phase entered", UVM_HIGH)
  super.build_phase(phase);
endfunction

task ai_core_lp_dma_sysspm_to_spm_test::main_phase(uvm_phase phase);
  super.main_phase(phase);
  phase.raise_objection(this);

  `uvm_info(get_type_name(), "Entered uvm main phase", UVM_LOW);
  uvm_sw_ipc_wait_event(16);
  `uvm_info(get_type_name(), "Received the event 16 from C test and DMA configurations and stimulus tranfer will start now", UVM_LOW);

  /* SYS SPM to SPM */
  stimulus_data_transfer("SYS_SPM", `SYSTEM_SPM_MEM_START_ADDR, DMA_MASTER_1, "SPM", `AI_CORE_SPM_MEM_START_ADDR+'h4_0000, DMA_MASTER_1, 'd0);

  `uvm_info(get_type_name(), "DMA transfers done, Generating event 1", UVM_LOW);
  uvm_sw_ipc_gen_event(1);


  phase.drop_objection(this);
endtask : main_phase

`endif	// __AI_CORE_LP_DMA_SYSSPM_TO_SPM_TEST__
