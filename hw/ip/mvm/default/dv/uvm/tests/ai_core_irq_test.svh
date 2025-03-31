// MVM basic test-case class
`ifndef __AI_CORE_IRQ_TEST__
`define __AI_CORE_IRQ_TEST__

/////////////////////////////////////////////////////////////////////////////////////////
// ai_core_irq_test
// Note : Introduced pound delay are uniform for all interrupt scenarios
//        @Deepak has observed in waveform and discussed with Designer during Alpha/Omega
//        For instance after setting the dedicated irq we have intodued 
//        delay 100 timestamp so we can correcly read irq_status.
//        200 timestamp delay after axi_write sequence completed and 
//        setting dedicated irq. 
/////////////////////////////////////////////////////////////////////////////////////////

 `define OFFSET_ERR_EXE_INP_OFFSET_SIZE_OVERFLOW  4
 `define OFFSET_ERR_EXE_OUP_OFFSET_SIZE_OVERFLOW  5

class ai_core_irq_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_irq_test)
  // Class constructor
  function new (string name="ai_core_irq_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_irq_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
     
      `uvm_info("MVM_IRQ_TEST",$sformatf("MVM irq starting"), UVM_HIGH)
      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;

      //ERR_IFD0_DPCMD_UNALIGNED_TLAST with irq generation
      if ( $test$plusargs("ERR_IFD0_DPCMD_UNALIGNED_TLAST") )  begin
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b000;
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

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
          burst_length == 'd7;
        };
        fork
          axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
        join_none
        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_ifd0_dpcmd_unaligned_tlast.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get()))  || ($countones(ral_read_data) < 1  ))
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_ifd0_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_ifd0_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_ifd0_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_ifd0_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_ifd0_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get() )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_ifd0_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifd0_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )

          axi_wr_seq.randomize() with {
            cfg_addr        == 28'h009_8000;
            sequence_length == 'd1;
            burst_size_enum_t == BURST_SIZE_64BIT;
            burst_type_enum_t == FIXED;
            burst_lenght_enum_t == BURST_LENGTH_1;
            cfg_data[0] == 64'h0000;
          };
          axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

          axi_wr_seq.randomize() with {
            cfg_addr        == 28'h009_1000;
            sequence_length == 'd1;
            burst_size_enum_t == BURST_SIZE_64BIT;
            burst_type_enum_t == INCR;
            burst_lenght_enum_t == BURST_LENGTH_2;
            cfg_data[0] == 64'h0000_0000_0000_0000;
            cfg_data[1] == 64'h01_0001_0000;
          };
          axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

          #200;
        end
      end

      //ERR_IFDW_DPCMD_UNALIGNED_TLAST with irq generation
      if ( $test$plusargs("ERR_IFDW_DPCMD_UNALIGNED_TLAST") )  begin
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b000;
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h00A_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h0000_0000_0000_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_master_stream_ifdw_base_seq.randomize() with {
           sequence_length == 1;
           //foreach (data[i]) data[i] == {512{1'b1}} ;
           burst_length == 'd128;
        };

        fork
          axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
        join_none
        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_ifdw_dpcmd_unaligned_tlast.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.get()))  || ($countones(ral_read_data) < 1  ))
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_ifdw_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_ifdw_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_ifdw_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_ifdw_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_ifdw_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.get() )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_ifdw_dpcmd_unaligned_tlast =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_ifdw_dpcmd_unaligned_tlast.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )

          axi_wr_seq.randomize() with {
            cfg_addr        == 28'h00A_1000;
            sequence_length == 'd1;
            burst_size_enum_t == BURST_SIZE_64BIT;
            burst_type_enum_t == INCR;
            burst_lenght_enum_t == BURST_LENGTH_2;
            cfg_data[0] == 64'h0000_0000_0000_0000;
            cfg_data[1] == 64'h0000_0000_0000_0000;
          };
          axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

          #200;
        end
      end

      //ERR_CONCURRENT_EXE_PRG_ON_WS with irq generation
      if ( $test$plusargs("ERR_CONCURRENT_EXE_PRG_ON_WS") )  begin
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b000;
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h00A_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h0000_0000_0000_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_master_stream_ifdw_base_seq.randomize() with {
           sequence_length == 1;
           burst_length == 'd64;
        };

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0001_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        axi_master_stream_ifd0_base_seq.randomize() with {
          sequence_length == 1;
          burst_length == 'd1;
        };


        fork
          axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
          axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
        join

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_concurrent_exe_prg_on_ws.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.get()))  || ($countones(ral_read_data) < 1  ))
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_concurrent_exe_prg_on_ws =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_concurrent_exe_prg_on_ws =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_concurrent_exe_prg_on_ws =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_concurrent_exe_prg_on_ws =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_concurrent_exe_prg_on_ws.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.get() )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_concurrent_exe_prg_on_ws =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_concurrent_exe_prg_on_ws.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

      //ERR_EXE_INP_OFFSET_SIZE_OVERFLOW with irq generation
      if ( $test$plusargs("ERR_EXE_INP_OFFSET_SIZE_OVERFLOW") )  begin
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b010;
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h1004;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0001_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
	 
       if(!axi_master_stream_ifd0_base_seq.randomize() with {
          sequence_length == 1;
          burst_length == 9;
         })
       axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
            
        #100;
	 
        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_inp_offset_size_overflow.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_inp_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_inp_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_inp_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h ral_read_data %h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_inp_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data), UVM_HIGH)
	   
          mvm_regmodel.m_mvmexe_regmod.irq_status.write(status, (1<<`OFFSET_ERR_EXE_INP_OFFSET_SIZE_OVERFLOW));

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
 
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_inp_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_inp_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_inp_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_inp_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_inp_offset_size_overflow.get())
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_inp_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_inp_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end    
       //ERR_EXE_OUP_OFFSET_SIZE_OVERFLOW with irq generation
      if ( $test$plusargs("ERR_EXE_OUP_OFFSET_SIZE_OVERFLOW") )  begin
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b010;
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'he040;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0001_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

       if(!axi_master_stream_ifd0_base_seq.randomize() with {
          sequence_length == 1;
          burst_length == 1;
         })
        `uvm_fatal("run_phase", "Failed to randomize");
        axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
	        
        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_oup_offset_size_overflow.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_oup_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_oup_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_oup_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_oup_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
         
          mvm_regmodel.m_mvmexe_regmod.irq_status.write(status, (1<<`OFFSET_ERR_EXE_OUP_OFFSET_SIZE_OVERFLOW));
	       
          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_oup_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_oup_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_oup_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_oup_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_oup_offset_size_overflow.get())
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_oup_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_oup_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

       //ERR_PRG_ROW_OFFSET_SIZE_OVERFLOW with irq generation
      if ( $test$plusargs("ERR_PRG_ROW_OFFSET_SIZE_OVERFLOW") )  begin
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h00A_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h0000_0007_0001_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_row_offset_size_overflow.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_prg_row_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_prg_row_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_row_offset_size_overflow.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_row_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_row_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_row_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.get() )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_prg_row_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_row_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

      //ERR_PRG_COL_OFFSET_SIZE_OVERFLOW with irq generation
      if ( $test$plusargs("ERR_PRG_COL_OFFSET_SIZE_OVERFLOW") )  begin
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h00A_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h0000_0700_0100_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_col_offset_size_overflow.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_prg_col_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_prg_col_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_col_offset_size_overflow.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_col_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_col_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_col_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.get() )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_prg_col_offset_size_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_col_offset_size_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

      //ERR_PRG_ILLEGAL_WEIGHT_SET with irq generation
      if ( $test$plusargs("ERR_PRG_ILLEGAL_WEIGHT_SET") )  begin
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b011;
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h00A_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h0000_0000_0000_0400;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_illegal_weight_set.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_prg_illegal_weight_set =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_prg_illegal_weight_set =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_illegal_weight_set.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_illegal_weight_set =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_illegal_weight_set =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_illegal_weight_set.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( !(mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.get()) )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_prg_illegal_weight_set =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_weight_set.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

     //ERR_PRG_ILLEGAL_CMD_OPCODE with irq generation
      if ( $test$plusargs("ERR_PRG_ILLEGAL_CMD_OPCODE") )  begin
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h00A_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h0000_0000_0000_0001;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_illegal_cmd_opcode.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_prg_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_prg_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_illegal_cmd_opcode.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_prg_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_prg_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( !(mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.get()) )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_prg_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_prg_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

      //ERR_EXE_ILLEGAL_CMD_OPCODE with irq generation
      if ( $test$plusargs("ERR_EXE_ILLEGAL_CMD_OPCODE") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0001_0002;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_cmd_opcode.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_cmd_opcode.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( !(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.get()) )
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_illegal_cmd_opcode =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_cmd_opcode.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end
      //x propagarion for omega improvements
      if ( $test$plusargs("X_PROPOGATION_TO_IFD0_WHEN_NO_QCMD_AVAILABLE") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0001_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        #100;
      end

      //ERR_EXE_QCMD_MEM_ADDR_OVERFLOW with irq generation
      if ( $test$plusargs("ERR_EXE_QCMD_MEM_ADDR_OVERFLOW") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_87F8;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0002_FF00;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_master_stream_ifd0_base_seq.randomize() with {
          sequence_length == 1;
          burst_length == 'd2;
        };
        fork
          axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
        join_none

        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_qcmd_mem_addr_overflow.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.get()))  || ($countones(ral_read_data) < 1 )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_qcmd_mem_addr_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_qcmd_mem_addr_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_qcmd_mem_addr_overflow.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_qcmd_mem_addr_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_qcmd_mem_addr_overflow =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_qcmd_mem_addr_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if(!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.get()) )
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_qcmd_mem_addr_overflow =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_qcmd_mem_addr_overflow.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
          `uvm_info("TEST_IRQ_CHECK"," err_exe_qcmd_mem_addr_overflow, calling $finish; For ifd0 sequence, tready return the x value so sequence will not not complete so calling $finish, this is improvement in design for omega to shield x propogation", UVM_HIGH)
          #1;
          $finish;
        end
      end

      //EXE_CMDBLK_CMD_DROPPED with irq generation
      if ( $test$plusargs("EXE_CMDBLK_CMD_DROPPED") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        for(int i=0;i<300;i++) begin
          axi_wr_seq.randomize() with {
            cfg_addr        == 28'h009_1000;
            sequence_length == 'd1;
            burst_size_enum_t == BURST_SIZE_64BIT;
            burst_type_enum_t == INCR;
            burst_lenght_enum_t == BURST_LENGTH_2;
            cfg_data[0] == 64'h0000_0000_0000_0000;
            cfg_data[1] == 64'h01_0001_0000;
          };
          axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        end

        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.exe_cmdblk_cmd_dropped.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for exe_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for exe_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_en.exe_cmdblk_cmd_dropped.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" exe_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" exe_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.exe_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.get() )
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for exe_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end
      
      //removed Remove SW bypass logic
      //TODO: removed commented code and clean up
      ////EXE_SWDP_CMD_DROPPED with irq generation
      //if ( $test$plusargs("EXE_SWDP_CMD_DROPPED") )  begin
      //  mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.exec_en.set(1'b1);;
      //  mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.sw_byp_en.set(1'b1);
      //  mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.update(status);

      //  for(int i=0;i<6;i++) begin
      //    axi_wr_seq.randomize() with {
      //      cfg_addr        == 28'h009_2000;
      //      sequence_length == 'd1;
      //      burst_size_enum_t == BURST_SIZE_64BIT;
      //      burst_type_enum_t == INCR;
      //      burst_lenght_enum_t == BURST_LENGTH_1;
      //      cfg_data[0] == 64'h18_0046_0003_0003;
      //    };
      //    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      //  end

      //  #200;

      //  mvm_regmodel.m_mvmexe_regmod.irq_en.exe_swdp_cmd_dropped.set(1'b1);
      //  mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

      //  #100;

      //  mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
      //  mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

      //  if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.get()))  || ($countones(ral_read_data) != 1  )) begin
      //    `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for exe_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
      //  end
      //  else begin
      //    `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for exe_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
      //    mvm_regmodel.m_mvmexe_regmod.irq_en.exe_swdp_cmd_dropped.set(1'b0);
      //    mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.set(1'b1);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

      //    mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
      //    mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

      //    `uvm_info("TEST_IRQ_CHECK",$sformatf(" exe_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
      //    `uvm_info("TEST_IRQ_CHECK",$sformatf(" exe_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.exe_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
      //    if( mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.get() )
      //      `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for exe_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.exe_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
      //    #200;
      //  end
      //end

     //PRG_CMDBLK_CMD_DROPPED with irq generation
      if ( $test$plusargs("PRG_CMDBLK_CMD_DROPPED") )  begin
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
        for(int i=0;i<300;i++) begin
          axi_wr_seq.randomize() with {
            cfg_addr        == 28'h00A_1000;
            sequence_length == 'd1;
            burst_size_enum_t == BURST_SIZE_64BIT;
            burst_type_enum_t == INCR;
            burst_lenght_enum_t == BURST_LENGTH_2;
            cfg_data[0] == 64'h0000_0000_0000_0000;
            cfg_data[1] == 64'h0000_0000_0000_0000;
          };
          axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        end
        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.prg_cmdblk_cmd_dropped.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for prg_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for prg_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_en.prg_cmdblk_cmd_dropped.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" prg_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" prg_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.prg_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.get() )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for prg_cmdblk_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_cmdblk_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

     //removed Remove SW bypass logic
     //TODO: removed commented code and clean up
     //PRG_SWDP_CMD_DROPPED with irq generation
      //if ( $test$plusargs("PRG_SWDP_CMD_DROPPED") )  begin
      //  mvm_regmodel.m_mvmprg_regmod.swdp_ctrl.exec_en.set(1'b1);;
      //  mvm_regmodel.m_mvmprg_regmod.swdp_ctrl.sw_byp_en.set(1'b1);
      //  mvm_regmodel.m_mvmprg_regmod.swdp_ctrl.update(status);
      //  for(int i=0;i<10;i++) begin
      //    axi_wr_seq.randomize() with {
      //      cfg_addr        == 28'h00A_2000;
      //      sequence_length == 'd1;
      //      burst_size_enum_t == BURST_SIZE_64BIT;
      //      burst_type_enum_t == INCR;
      //      burst_lenght_enum_t == BURST_LENGTH_1;
      //      cfg_data[0] == {1'b0,2'b00,i[15:0],{14{1'b0}},2'b11};
      //    };
      //    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      //  end
      //  #200;

      //  mvm_regmodel.m_mvmexe_regmod.irq_en.prg_swdp_cmd_dropped.set(1'b1);
      //  mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
      //  #100;

      //  mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
      //  mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

      //  if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.get()))  || ($countones(ral_read_data) != 1  )) begin
      //    `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for prg_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
      //  end
      //  else begin
      //    `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for prg_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.set(1'b1);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
      //    mvm_regmodel.m_mvmexe_regmod.irq_en.prg_swdp_cmd_dropped.set(1'b0);
      //    mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

      //    mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
      //    mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
      //    mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

      //    `uvm_info("TEST_IRQ_CHECK",$sformatf(" prg_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
      //    `uvm_info("TEST_IRQ_CHECK",$sformatf(" prg_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.prg_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
      //    if( mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.get() )
      //     `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for prg_swdp_cmd_dropped =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.prg_swdp_cmd_dropped.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
      //    #200;
      //  end
      //end

     //DBG_SW_INTERRUPT with irq generation
      if ( $test$plusargs("DBG_SW_INTERRUPT") )  begin
        mvm_regmodel.m_mvmexe_regmod.irq_en.dbg_sw_interrupt.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
        mvm_regmodel.m_mvmexe_regmod.dp_ctrl.dbg_sw_irq.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.dp_ctrl.update(status);
        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.get()))  || ($countones(ral_read_data) != 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for dbg_sw_interrupt =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for dbg_sw_interrupt =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_en.dbg_sw_interrupt.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" dbg_sw_interrupt =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_HIGH)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" dbg_sw_interrupt =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.dbg_sw_interrupt.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_HIGH)
          if( !(mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.get()) )
           `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for dbg_sw_interrupt =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.dbg_sw_interrupt.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

      //ERR_EXE_ILLEGAL_QCMD_PTR with irq generation
      if ( $test$plusargs("ERR_EXE_ILLEGAL_QCMD_PTR") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b010;

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0001_0100;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_start.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_illegal_loop_start =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_illegal_loop_start =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_LOW)
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_start.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_loop_start =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_LOW)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_loop_start =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_start.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_LOW)
          if( !(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.get()) )
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_illegal_loop_start =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_start.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end

      //err_exe_illegal_loop_len with irq generation
      if ( $test$plusargs("ERR_EXE_ILLEGAL_LOOP_LEN") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b010;

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h01_0000_0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_len.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_illegal_loop_len =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_illegal_loop_len =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_LOW)
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_len.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_loop_len =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_LOW)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_loop_len =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_len.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_LOW)
          if( !(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.get()) )
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_illegal_loop_len =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_len.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end


      //ERR_EXE_ILLEGAL_LOOP_ITER with irq generation
      if ( $test$plusargs("ERR_EXE_ILLEGAL_LOOP_ITER") )  begin
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
        mvm_utils_vif.disable_assertion_for_irq=1;
        mvm_utils_vif.assrt_ctrl = 3'b010;

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_8000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == FIXED;
          burst_lenght_enum_t == BURST_LENGTH_1;
          cfg_data[0] == 64'h0000;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

        axi_wr_seq.randomize() with {
          cfg_addr        == 28'h009_1000;
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_2;
          cfg_data[0] == 64'h0000_0000_0000_0000;
          cfg_data[1] == 64'h00_0000_0100;
        };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


        #200;

        mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_iter.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);

        #100;

        mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
        mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

        if( (!(mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.get()))  || ($countones(ral_read_data) < 1  )) begin
          `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq generated for err_exe_illegal_loop_iter =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
        end
        else begin
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" Irq generated for err_exe_illegal_loop_iter =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_LOW)
          mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_iter.set(1'b0);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.set(1'b1);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          mvm_regmodel.m_mvmexe_regmod.irq_en.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_en.update(status);
          mvm_regmodel.m_mvmexe_regmod.irq_status.read(status, ral_read_data);
          mvm_regmodel.m_mvmexe_regmod.irq_status.update(status);

          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_loop_iter =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value()), UVM_LOW)
          `uvm_info("TEST_IRQ_CHECK",$sformatf(" err_exe_illegal_loop_iter =%0h, desired=0x%0h mirrored=0x%0h",mvm_regmodel.m_mvmexe_regmod.irq_en.err_exe_illegal_loop_iter.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get(), mvm_regmodel.m_mvmexe_regmod.irq_en.get_mirrored_value()), UVM_LOW)
          if(!( mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.get()) )
            `uvm_error("TEST_IRQ_CHECK",$sformatf(" No Irq cleared for err_exe_illegal_loop_iter =%0h, desired=0x%0h mirrored=0x%0h,ral_read_data=%0h",mvm_regmodel.m_mvmexe_regmod.irq_status.err_exe_illegal_loop_iter.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get(), mvm_regmodel.m_mvmexe_regmod.irq_status.get_mirrored_value(),ral_read_data ) )
          #200;
        end
      end
      

      `uvm_info("MVM_IRQ_TEST",$sformatf("MVM irq end"), UVM_HIGH)

    phase.drop_objection(this);
  endtask

endclass:ai_core_irq_test

`endif	// __AI_CORE_IRQ_TEST__
