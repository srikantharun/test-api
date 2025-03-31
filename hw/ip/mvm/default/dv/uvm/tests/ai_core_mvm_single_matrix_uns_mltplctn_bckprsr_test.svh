// MVM basic test-case class
// Backpressure test
//Applying delayed sequence for IAU interface in a multiplication test, so that IAU does not accept output from MVM.
//This results in banks going inactive inside the MVM. After ready getting asserted banks go active again
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_UNS_MLTPLCTN__TEST__
`define __AI_CORE_MVM_SINGLE_MATRIX_UNS_MLTPLCTN__TEST__

`include "uvm_macros.svh"

class ai_core_mvm_single_matrix_uns_mltplctn_bckprsr_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_uns_mltplctn_bckprsr_test)
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_uns_mltplctn_bckprsr_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_single_matrix_uns_mltplctn_bckprsr_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_delay_sequence::type_id::get());
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication starting"), UVM_HIGH)
      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;
      
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, 0);
      mvm_regmodel.m_mvmprg_regmod.dp_ctrl.write(status, 0);
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h00A_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h0000_0000_0000_0000;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
         foreach (data[i]) data[i] == {512{1'b1}} ;
         burst_length == 'd64;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_HIGH);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

     wait_for_prg_status();

      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_8000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 64'h0000;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h01_0001_0000;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifd0_base_seq.randomize() with {
        sequence_length == 1;
        foreach (data[i]) data[i] == {512{1'b1}} ;
        burst_length == 'd1;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);

      wait_for_exe_status();

      check_irq_status();
     
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication end"), UVM_HIGH)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_single_matrix_uns_mltplctn_bckprsr_test

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_UNS_MLTPLCTN_BCKPRSR_TEST__
