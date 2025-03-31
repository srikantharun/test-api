// MVM basic test-case class
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_INT16_TEST__
`define __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_INT16_TEST__

class ai_core_mvm_single_matrix_multiplication_int16_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_multiplication_int16_test)
   
 
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_multiplication_int16_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_single_matrix_multiplication_int16_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication int16 starting"), UVM_LOW)
      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;

      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, 0);
      mvm_regmodel.m_mvmprg_regmod.dp_ctrl.write(status, 0);
      if (!mvm_prg_cmd_tb_data_h.randomize with {mvm_prg_cmd_struct.wb_t_pw == 1;
					     mvm_prg_cmd_struct.wb_u_pw == 1;
					     mvm_prg_cmd_struct.a_t_pw ==0;
					     mvm_prg_cmd_struct.a_u_pw ==0;	
   		                             mvm_prg_cmd_struct.a_s == 0;
					     mvm_prg_cmd_struct.extra ==0;
						})
        `uvm_fatal("run_phase", "Failed to randomize the prg cmd struct");
          
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_PRG_CMDB_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] ==  mvm_prg_cmd_tb_data_h.mvm_prg_cmd_data;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
         //TO DO update the ifdw data to random value once the Design is stable with int16 matrix multiplication
         foreach (data[i]) data[i] == {{496{1'b0}},{16{1'b1}}} ;							    
         burst_length == 'd256;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);


      wait_for_prg_status();

      if (!mvm_exe_instr_tb_data_h.randomize with {mvm_exe_instr_struct.wb_t_pw == 1;
					         mvm_exe_instr_struct.wb_u_pw == 1;
					         mvm_exe_instr_struct.a_t_pw ==0;
					         mvm_exe_instr_struct.a_u_pw ==0;	
   		                                 mvm_exe_instr_struct.a_s == 0;
						})
        `uvm_fatal("run_phase", "Failed to randomize the exe instr");               
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_INSTR_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == mvm_exe_instr_tb_data_h.mvm_exe_instr_data;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
  
      if (!mvm_exe_cmd_tb_data_h.randomize with {mvm_exe_cmd_struct.loop_ptr == 0;
					         mvm_exe_cmd_struct.loop_len == 1;
					         mvm_exe_cmd_struct.loop_iter ==3;
					         mvm_exe_cmd_struct.extra == 'hC;	
						 })
	`uvm_fatal("run_phase", "Failed to randomize");	
	
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_CMDB_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0100;
        cfg_data[1] == mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data;    
      }) 
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifd0_base_seq.randomize() with {
        sequence_length == 1;
        //TO DO update the ifd0 data to random value once the Design is stable with int16 matrix multiplication
        foreach (data[i]) data[i] == {{496{1'b0}},{16{1'b1}}} ; 
        burst_length == 'd12;  //As it is int 16 design is expecting 12 beats instead 6 beats like in int8 multiplication
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);

      wait_for_exe_status();
      
      check_irq_status();

      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication int16 end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_single_matrix_multiplication_int16_test

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_INT16_TEST__
