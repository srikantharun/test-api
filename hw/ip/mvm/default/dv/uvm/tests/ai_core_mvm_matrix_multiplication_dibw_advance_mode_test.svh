// MVM basic test-case class
`ifndef __AI_CORE_MVM_MATRIX_MULTIPLICATION_DIBW_ADVANCE_MODE_TEST__
`define __AI_CORE_MVM_MATRIX_MULTIPLICATION_DIBW_ADVANCE_MODE_TEST__

//Note - TEST follows :
//the offset and length of the two matrixes are randomly selected
//the instruction is using the same values (offset and length) randomized at the test level (TODO needs to be a subset of the matrix randomized)

class ai_core_mvm_matrix_multiplication_dibw_advance_mode_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_matrix_multiplication_dibw_advance_mode_test)
  rand bit [COL_OFF-1:0]              col_off_ifd0, col_off_ifd2, row_off_ifd0, row_off_ifd2;
  rand bit [MATRIX_LEN-1:0]           col_len_ifd0, col_len_ifd2, row_len_ifd0, row_len_ifd2;
  int col_off_ifd0_intr,col_len_ifd0_intr, col_off_ifd2_intr,col_len_ifd2_intr, row_off_ifd0_intr,row_len_ifd0_intr, row_off_ifd2_intr,row_len_ifd2_intr;
  rand bit [1:0] wet_set_ifd0, wet_set_ifd2;
  rand bit signed_unsigned_operation;
  int wet_set_ifd0_intr, wet_set_ifd2_intr;
  int mvm_iterations;

  constraint row_off_len { row_len_ifd0>=0;
                           row_len_ifd2>=0; 
                           row_off_ifd0 + row_len_ifd0<9;
                           row_off_ifd2 + row_len_ifd2<9;
                         }

  constraint max_utilisation { solve col_off_ifd0 before col_off_ifd2;
                               solve col_len_ifd0 before col_len_ifd2;
                               col_len_ifd0>=0;
                               col_len_ifd2>=0;
                               col_off_ifd0 + col_len_ifd0 + col_off_ifd2 + col_len_ifd2 < 8; 
                               wet_set_ifd0<4; 
                               wet_set_ifd2<4; }

  constraint ifd2_seletion   { 
                                (col_off_ifd2 + col_len_ifd2 < col_off_ifd0) || 
                                (col_off_ifd2> col_off_ifd0+col_len_ifd0 ) 
                                  ; 
                             }

  //// Class constructor
  function new (string name="ai_core_mvm_matrix_multiplication_dibw_advance_mode_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_matrix_multiplication_dibw_advance_mode_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
    if(!$value$plusargs("MVM_ITERATIONS=%0d", mvm_iterations)) mvm_iterations = 5;
     
    for(int i=0; i< mvm_iterations; i++) begin 
    
      void'(randomize());

      `uvm_info("MVM_single_TEST",$sformatf("MVM ai_core_mvm_matrix_multiplication_dibw_advance_mode_test matrix multiplication starting"), UVM_LOW)
      
      col_off_ifd0_intr = {5'b0,col_off_ifd0};
      col_len_ifd0_intr = {5'b0,col_len_ifd0};
      col_off_ifd2_intr = {5'b0,col_off_ifd2};
      col_len_ifd2_intr = {5'b0,col_len_ifd2};
      
      row_off_ifd0_intr = {4'b0,row_off_ifd0};
      row_len_ifd0_intr = {4'b0,row_len_ifd0};
      row_off_ifd2_intr = {4'b0,row_off_ifd2};
      row_len_ifd2_intr = {4'b0,row_len_ifd2};
      
      wet_set_ifd0_intr = {6'b0,wet_set_ifd0};
      wet_set_ifd2_intr = {6'b0,wet_set_ifd2};

      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;
    
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, signed_unsigned_operation);
      mvm_regmodel.m_mvmprg_regmod.dp_ctrl.write(status, signed_unsigned_operation);
      uvm_report_info(get_type_name(), $psprintf("ifd0_col_off is  = %0d,ifd0_col_len =%0d, ifd0_row_off is  = %0d,ifd0_row_len =%0d ", col_off_ifd0, col_len_ifd0, row_off_ifd0, row_len_ifd0 ), UVM_HIGH);
      uvm_report_info(get_type_name(), $psprintf("ifd2_col_off is  = %0d,ifd2_col_len =%0d, ifd2_row_off is  = %0d,ifd2_row_len =%0d  and signed_unsigned_operation=%0d", col_off_ifd2, col_len_ifd2, row_off_ifd2, row_len_ifd2, signed_unsigned_operation ), UVM_HIGH);

      if (!mvm_prg_cmd_tb_data_h.randomize with {mvm_prg_cmd_struct.wb_t_pw == col_len_ifd0_intr;
					                                       mvm_prg_cmd_struct.wb_u_pw == row_len_ifd0_intr;
					                                       mvm_prg_cmd_struct.a_t_pw == col_off_ifd0_intr;
					                                       mvm_prg_cmd_struct.a_u_pw == row_off_ifd0_intr;
                                                 mvm_prg_cmd_struct.a_s == wet_set_ifd0_intr;
					                                       mvm_prg_cmd_struct.extra == extra;
						                                     })
      `uvm_fatal("run_phase", "Failed to randomize the prg cmd struct");     
      
      `uvm_info(get_type_name(), $psprintf("mvm_prg_cmd_tb_data_h = \n %s", mvm_prg_cmd_tb_data_h.sprint()), UVM_LOW);
          
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
      
      uvm_report_info(get_type_name(), $psprintf("IFDW0 first PRG sequence getting started"), UVM_HIGH);

      if(!axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
         burst_length == (col_len_ifd0+1) * (row_len_ifd0+1) * 64;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
      
      uvm_report_info(get_type_name(), $psprintf("IFDW0 first PRG STATUS READ FINISHED axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      uvm_report_info(get_type_name(), $psprintf("ifd0_col_off is  = %0d,ifd0_col_len =%0d ", col_off_ifd0, col_len_ifd0 ), UVM_HIGH);
      
      wait_for_prg_status();

      //prgrmng for idf2

      if (!mvm_prg_cmd_tb_data_h.randomize with {mvm_prg_cmd_struct.wb_t_pw == col_len_ifd2_intr;
					                                       mvm_prg_cmd_struct.wb_u_pw == row_len_ifd2_intr;
					                                       mvm_prg_cmd_struct.a_t_pw == col_off_ifd2_intr;
					                                       mvm_prg_cmd_struct.a_u_pw == row_off_ifd2_intr;
                                                 mvm_prg_cmd_struct.a_s == wet_set_ifd2_intr;
					                                       mvm_prg_cmd_struct.extra == extra;
						                                    })
      `uvm_fatal("run_phase", "Failed to randomize the prg cmd struct");     
      
      `uvm_info(get_type_name(), $psprintf("mvm_prg_cmd_tb_data_h = \n %s", mvm_prg_cmd_tb_data_h.sprint()), UVM_LOW);
          
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
         burst_length == (col_len_ifd2+1) * (row_len_ifd2+1) * 64;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
      
      uvm_report_info(get_type_name(), $psprintf("IFDW second PRG STATUS READ Done axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      uvm_report_info(get_type_name(), $psprintf("ifd2_col_off is  = %0d,ifd2_col_len =%0d ", col_off_ifd2, col_len_ifd2 ), UVM_HIGH);
      wait_for_prg_status();
      
      if (!mvm_exe_instr_tb_data_h.randomize with {mvm_exe_instr_struct.wb_t_pw == col_len_ifd0;
					                                         mvm_exe_instr_struct.wb_u_pw == row_len_ifd0;
					                                         mvm_exe_instr_struct.a_t_pw == col_off_ifd0;
					                                         mvm_exe_instr_struct.a_u_pw == row_off_ifd0;
                                                   mvm_exe_instr_struct.a_s == wet_set_ifd0;
						                                      })
        `uvm_fatal("run_phase", "Failed to randomize the exe instr");               
      
        `uvm_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_h = \n %s", mvm_exe_instr_tb_data_h.sprint()), UVM_HIGH);
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

      if (!mvm_exe_instr_tb_data_h.randomize with {mvm_exe_instr_struct.wb_t_pw == col_len_ifd2;
					                                         mvm_exe_instr_struct.wb_u_pw == row_len_ifd2;
					                                         mvm_exe_instr_struct.a_t_pw == col_off_ifd2;
					                                         mvm_exe_instr_struct.a_u_pw == row_off_ifd2;
                                                   mvm_exe_instr_struct.a_s == wet_set_ifd2;
						                                      })
        `uvm_fatal("run_phase", "Failed to randomize the exe instr");               
      
        `uvm_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_h = \n %s", mvm_exe_instr_tb_data_h.sprint()), UVM_HIGH);
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_INSTR_START_ADDR + 2; //second addr for ifd2
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == mvm_exe_instr_tb_data_h.mvm_exe_instr_data;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


      if (!mvm_exe_cmd_tb_data_h.randomize with {mvm_exe_cmd_struct.loop_ptr == 0;
					                                       mvm_exe_cmd_struct.loop_len == 2; // utilising first two instrution
					                                       mvm_exe_cmd_struct.loop_iter < 3; //loop_iter
					                                       mvm_exe_cmd_struct.extra == 3; // DIBW enable and advance mode selected
						                                    })
	  `uvm_fatal("run_phase", "Failed to randomize");	
      `uvm_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
	
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_CMDB_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data;    
      }) 
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


      fork 
        begin 
          if(!axi_master_stream_ifd0_base_seq.randomize() with {
            sequence_length == 1;
            burst_length == mvm_exe_cmd_tb_data_h.mvm_exe_cmd_struct.loop_iter * (row_len_ifd0+1);
          })
            `uvm_fatal("run_phase", "Failed to randomize");
          axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
        end 
     
        begin
          if(!axi_master_stream_ifd2_base_seq.randomize() with {
            sequence_length == 1;
            burst_length == mvm_exe_cmd_tb_data_h.mvm_exe_cmd_struct.loop_iter * (row_len_ifd2+1);
          })
            `uvm_fatal("run_phase", "Failed to randomize");
          axi_master_stream_ifd2_base_seq.start(env.axi_system_env.master[3].sequencer);
        end
      join 
     
      `uvm_info("MVM_single_TEST",$sformatf("starting wait_for_exe_status api at end"), UVM_HIGH)
      wait_for_exe_status();
      `uvm_info("MVM_single_TEST",$sformatf("completed wait_for_exe_status api at end"), UVM_HIGH)
      
      check_irq_status();

      `uvm_info("MVM_single_TEST",$sformatf("MVM single matrix multiplication end for i = %0d",i), UVM_HIGH)
    end

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_matrix_multiplication_dibw_advance_mode_test

`endif	// __AI_CORE_MVM_MATRIX_MULTIPLICATION_DIBW_ADVANCE_MODE_TEST__
