// MVM basic test-case class
`ifndef __AI_CORE_MVM_SIGNED_SINGLE_MATRIX_MULTIPLICATION_TEST__
`define __AI_CORE_MVM_SIGNED_SINGLE_MATRIX_MULTIPLICATION_TEST__

class ai_core_mvm_signed_single_matrix_multiplication_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_signed_single_matrix_multiplication_test)
  // Class constructor
  function new (string name="ai_core_mvm_signed_single_matrix_multiplication_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_signed_single_matrix_multiplication_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication starting"), UVM_LOW)
      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;
      // Perform writes and reads
      //axi_slave_stream_iau_base_seq.randomize();
      //fork
      //axi_slave_stream_iau_base_seq.start(env.axi_system_env.slave[0].sequencer);
      //join_none

      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.write(status, ral_write_data);
      axi_wr_seq.randomize() with {
        cfg_addr        == 28'h00A_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h0000_0101_0000_0000;
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
         foreach (data[i]) data[i] == {512{1'b1}} ;
         burst_length == 'd256;
      };
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

      wait_for_prg_status();
     
      axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_8000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 64'h2200;
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


      axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h03_0001_0000;
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      axi_master_stream_ifd0_base_seq.randomize() with {
        sequence_length == 1;
        //foreach (data[i]) data[i] == {512{1'b1}} ;
        //foreach (data[i]) data[i] == {{504{1'b0}},{8{1'b1}}} ;
        burst_length == 'd6;
      };
      axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);

      wait_for_exe_status();

      check_irq_status();

      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_signed_single_matrix_multiplication_test

`endif	// __AI_CORE_MVM_SIGNED_SINGLE_MATRIX_MULTIPLICATION_TEST__
