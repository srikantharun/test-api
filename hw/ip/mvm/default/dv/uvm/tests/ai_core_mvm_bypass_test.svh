// MVM basic test-case class
`ifndef __AI_CORE_MVM_BYPASS_TEST__
`define __AI_CORE_MVM_BYPASS_TEST__

class ai_core_mvm_bypass_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_bypass_test)
  int beat_transfer;
  // Class constructor
  function new (string name="ai_core_mvm_bypass_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_bypass_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
      `uvm_info("AI_CORE_MVM_BYPASS_TEST",$sformatf("MVM ai_core_mvm_bypass_test starting"), UVM_LOW)
      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;

      //axi_wr_seq.randomize() with {
      //  cfg_addr        == 28'h009_8000;
      //  sequence_length == 'd1;
      //  burst_size_enum_t == BURST_SIZE_64BIT;
      //  burst_type_enum_t == FIXED;
      //  burst_lenght_enum_t == BURST_LENGTH_1;
      //  cfg_data[0] == 64'h0000;
      //};
      //axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
     
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 64'h0009_0000_0000_0000;       				       
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      void'(std::randomize(beat_transfer) with { beat_transfer inside {[1:100]};});
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        if(!axi_master_stream_ifd0_base_seq.randomize() with {
        sequence_length == 1;
        burst_length == beat_transfer;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      fork
        axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
      join_none
      //// Perform writes and reads
      //axi_slave_stream_iau_base_seq.randomize();
      //fork
      //axi_slave_stream_iau_base_seq.start(env.axi_system_env.slave[0].sequencer);
      //join_none
      #100;
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data);
     
      wait_for_exe_status();

      check_irq_status();
     
      //removed Remove SW bypass logic
      //TODO: removed commented code and clean up
      //if ( $test$plusargs("no_refmodel_check_for_exe_software_bypass") )  begin //TODO in next project
      //  // swdp with exe
      //  mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.exec_en.set(1'b1);;
      //  mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.sw_byp_en.set(1'b1);
      //  mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.update(status);

      //  axi_master_stream_ifd0_base_seq.randomize() with {
      //    sequence_length == 1;
      //    //foreach (data[i]) data[i] == {512{1'b1}} ;
      //    burst_length == 'd10;
      //  };
      //  fork
      //    axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
      //  join_none

      //if ( $test$plusargs("swdp_with_bypass_sign_extends_without_tlast") )  begin //TODO in next project
      //  axi_wr_seq.randomize() with {
      //    cfg_addr        == 28'h009_2000;
      //    sequence_length == 'd1;
      //    burst_size_enum_t == BURST_SIZE_64BIT;
      //    burst_type_enum_t == INCR;
      //    burst_lenght_enum_t == BURST_LENGTH_1;
      //    cfg_data[0] == 64'h00_0001_0000_0000;
      //  };
      //  axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      //  mvm_regmodel.m_mvmexe_regmod.irq_en.err_ifd0_dpcmd_unaligned_tlast.set(1'b1);
      //  mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
      //  do begin
      //    ral_read_data   = 64'h000_0000;
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
      //   if(ral_read_data[0])  begin mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.set(1'b1);  end
      //  end while(!ral_read_data[0]);
      //  if(!(ral_read_data[0] ))  //if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get())) )
      //    `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_ifdO_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value() ) )
      //  else begin
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.set(1'b1);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
      //  end
      //end
      //else begin
      //  axi_wr_seq.randomize() with {
      //    cfg_addr        == 28'h009_2000;
      //    sequence_length == 'd1;
      //    burst_size_enum_t == BURST_SIZE_64BIT;
      //    burst_type_enum_t == INCR;
      //    burst_lenght_enum_t == BURST_LENGTH_1;
      //    cfg_data[0] == 64'h00_0005_0000_0000;
      //  };
      //  axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      //end
        #300;


      //end //testplusarg
      `uvm_info("AI_CORE_MVM_BYPASS_TEST",$sformatf("MVM ai_core_mvm_bypass_test end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_bypass_test

`endif	// __AI_CORE_MVM_BYPASS_TEST__
