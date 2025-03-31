// MVM basic test-case class
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_BROADCAST_TEST__
`define __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_BROADCAST_TEST__

class ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_broadcast_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_broadcast_test)
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_broadcast_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_broadcast_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication starting"), UVM_LOW)
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
        cfg_data[1] == 64'h0000_0001_0000_0008; //weight set 0 and extra 8 (simple mode
        })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
         foreach (data[i]) data[i] == {8{1'b1}} ;
         //foreach (data[i]) data[i] == {{504{1'b0}},{8{1'b1}}} ;							    
         burst_length == 'd128;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("IFDW0 PRG axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

      wait_for_prg_status();

      uvm_report_info(get_type_name(), $psprintf("IFDW0 first PRG STATUS READ FINISHED axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);

      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_8000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 64'h0200;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      uvm_report_info(get_type_name(), $psprintf("exeution instrution sequence completed"), UVM_LOW);

      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h0100_0003_0001_0000; //simple mode / loop_iter 3 / loop_len 1 / loop_strt 0
      }) 
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      `uvm_info(get_type_name(), $psprintf("exeution command sequence completed"), UVM_LOW);

      fork 
        begin 
          if(!axi_master_stream_ifd0_base_seq.randomize() with {
            sequence_length == 1;
            foreach (data[i]) data[i] == {512{1'b1}} ;
            //foreach (data[i]) data[i] == {{504{1'b0}},{8{1'b1}}} ;
            burst_length == 'd6;
          })
            `uvm_fatal("run_phase", "Failed to randomize");
          axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
        end 
     
        begin
          if(!axi_master_stream_ifd2_base_seq.randomize() with {
            sequence_length == 1;
            foreach (data[i]) data[i] == {{504{1'b0}},{8{1'b1}}} ;
            burst_length == 'd6;
          })
            `uvm_fatal("run_phase", "Failed to randomize");
          axi_master_stream_ifd2_base_seq.start(env.axi_system_env.master[3].sequencer);
        end
      join 
      `uvm_info(get_type_name(), $psprintf("IFD0_2  axi_master_stream_sequence completed"), UVM_LOW);
     
      wait_for_exe_status();
      
      check_irq_status();
     
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_broadcast_test

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_BROADCAST_TEST__


