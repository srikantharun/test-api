// MVM prgmode 1 test does the TUu multiplication
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_PRGMODE_1_TEST__
`define __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_PRGMODE_1_TEST__

class ai_core_mvm_single_matrix_multiplication_prgmode_1_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_multiplication_prgmode_1_test)
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_multiplication_prgmode_1_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_single_matrix_multiplication_prgmode_1_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication starting"), UVM_LOW)

     
      configure_prg_reg();
      configure_exe_reg();     
      unsigned_exe_prg_enable();
     
     if (!mvm_prg_cmd_tb_data_h.randomize with {mvm_prg_cmd_struct.wb_t_pw == col_len_intr-1;
					     mvm_prg_cmd_struct.wb_u_pw == row_len_intr-1;
					     mvm_prg_cmd_struct.a_t_pw == col_off_intr;
					     mvm_prg_cmd_struct.a_u_pw == row_off_intr;	
   		                             mvm_prg_cmd_struct.a_s == weight_set_intr;
					     mvm_prg_cmd_struct.extra == 1; //extra byte has prgmode 1
						})
      `uvm_fatal("run_phase", "Failed to randomize the prg cmd struct");      
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_PRG_CMDB_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == mvm_prg_cmd_tb_data_h.mvm_prg_cmd_data; //64'h0000_0708_0000_0001;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
	 burst_length == col_len * row_len * 64; // 'd4608;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

      wait_for_prg_status();
      if (!mvm_exe_instr_tb_data_h.randomize with {mvm_exe_instr_struct.wb_t_pw == col_len-1;
					           mvm_exe_instr_struct.wb_u_pw == row_len-1;
					           mvm_exe_instr_struct.a_t_pw == col_off;
					           mvm_exe_instr_struct.a_u_pw == row_off;	
   		                                   mvm_exe_instr_struct.a_s == weight_set;
						})
        `uvm_fatal("run_phase", "Failed to randomize the exe instr");                     
        `uvm_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_h = \n %s", mvm_exe_instr_tb_data_h.sprint()), UVM_HIGH);	
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_8000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] ==  mvm_exe_instr_tb_data_h.mvm_exe_instr_data; //64'hF000;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if (!mvm_exe_cmd_tb_data_h.randomize with {mvm_exe_cmd_struct.loop_ptr == 0;
					         mvm_exe_cmd_struct.loop_len == 1;
					         mvm_exe_cmd_struct.loop_iter < 3;
						 })
	  `uvm_fatal("run_phase", "Failed to randomize");	
      `uvm_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data; //64'h0000_0003_0001_0000;
      }) 
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifd0_base_seq.randomize() with {
        sequence_length == 1;
        burst_length == mvm_exe_cmd_tb_data_h.mvm_exe_cmd_struct.loop_iter * row_len; //'d27;		 
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);

      wait_for_exe_status();

      check_irq_status();

      if(mvm_if.prgmode == TUu) begin
	`uvm_info("PRGMODE",$sformatf("prgmode test not set %s", mvm_if.prgmode),UVM_LOW)
      end else begin
	`uvm_error("PRG MODE","Mismatch is prgmode") 	   
      end
     
     
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_single_matrix_multiplication_prgmode_1_test

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_TEST__
