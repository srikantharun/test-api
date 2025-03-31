// MVM basic test-case class
`ifndef __AI_CORE_MVM_RANDOM_ROW_COL_MATRIX_MULTIPLICATION_TEST__
`define __AI_CORE_MVM_RANDOM_ROW_COL_MATRIX_MULTIPLICATION_TEST___

class ai_core_mvm_random_row_col_matrix_multiplication_test extends ai_core_mvm_base_test;
  bit [2:0]  col, loop_iter;
  bit [3:0] row;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_random_row_col_matrix_multiplication_test)
  // Class constructor
  function new (string name="ai_core_mvm_random_row_col_matrix_multiplication_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_row_col_matrix_multiplication_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    void'(randomize());      
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    
      void'(std::randomize(row) with { row inside {[0:7]};});
      void'(std::randomize(col) with { col inside {[0:8]};});
      void'(std::randomize(loop_iter) with { loop_iter inside {[1:8]};});

      `uvm_info("MVM_RANDOM_SW_TEST_MODE_TEST",$sformatf("MVM random row_col matrix multiplication starting"), UVM_HIGH)
      #100ns;
      ral_write_data = 64'h000_0001;
      configure_prg_reg;
      configure_exe_reg;
      prepare_prg_packet_and_send_ifdw;
      wait_for_prg_status;

      prepare_exe_instr;
      prepare_exe_packet_and_send_ifd0;
      wait_for_exe_status;
     
      check_irq_status();

      `uvm_info("MVM_RANDOM_test",$sformatf("MVM random row_col matrix multiplication end"), UVM_HIGH)
    phase.drop_objection(this);
  endtask

  task configure_prg_reg;
    int delay;
      begin
        void'(std::randomize(delay) with { delay inside {[0:300]};});
        #(delay * 10ns);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
      end
  endtask

  task configure_exe_reg;
    int delay;
    begin
      void'(std::randomize(delay) with { delay inside {[0:300]};});
      #(delay * 10ns);
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
    end
  endtask

  task prepare_prg_packet_and_send_ifdw;
    axi_wr_seq.randomize() with {
      cfg_addr        == MVM_PRG_CMDB_START_ADDR ;
      sequence_length == 'd1;
      burst_size_enum_t == BURST_SIZE_64BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_2;
      cfg_data[0] == 64'h0000_0000_0000_0000;
      cfg_data[1] == {16'b0, 5'b0, col, 4'b0, row, 32'b0};
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
    `uvm_info("MVM_RANDOM_test",$sformatf("value of col is %0b and row is %0b", col, row ), UVM_HIGH)
    `uvm_info("MVM_RANDOM_test",$sformatf("value of cfg data is %0b", axi_wr_seq.rsp.data[1]  ), UVM_HIGH)
    `uvm_info(get_type_name(), $psprintf("axi_wr_seq = \n %s", axi_wr_seq.sprint()), UVM_HIGH);
         begin
           key.get(1);
           send_ifdw_packet;
           key.put(1);
         end
  endtask

  task send_ifdw_packet;
    begin
      axi_master_stream_ifdw_base_seq.randomize() with { sequence_length == 1;
            burst_length ==  64 * ((row+1) * (col+1));
            };
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_HIGH);
      `uvm_info("MVM_RANDOM_test",$sformatf("value of col is %0b and row is %0b", col, row ), UVM_HIGH)
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
    end
  endtask

  task prepare_exe_instr;
     // ==========QCommand packet=====================//mvm_exe_instr_addr.size

      axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_INSTR_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == {col, row, 9'b0};
      };
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
    `uvm_info("MVM_RANDOM_test",$sformatf("value of col is %0b and row is %0b", col, row ), UVM_HIGH)
    `uvm_info("MVM_RANDOM_test",$sformatf("value of cfg data is %0b", axi_wr_seq.rsp.data[0]  ), UVM_HIGH)
    `uvm_info(get_type_name(), $psprintf("axi_wr_seq = \n %s", axi_wr_seq.sprint()), UVM_HIGH);
  endtask

  task prepare_exe_packet_and_send_ifd0;
    // ==========EXE command packet=====================//
    configure_exe_cmdb_packet;
    //Create the exe command packet
    send_ifd0_packet;
      // ==============================================//
  endtask

  task configure_exe_cmdb_packet;
    axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_CMDB_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == {29'b0, loop_iter, 16'b1, 16'b0};
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
    `uvm_info("MVM_RANDOM_test",$sformatf("value of loop_iter is %0b", loop_iter ), UVM_HIGH)
    `uvm_info(get_type_name(), $psprintf("axi_wr_seq from 127 line = \n %s", axi_wr_seq.sprint()), UVM_HIGH);
  endtask

  task send_ifd0_packet;
    bit [7:0] ptr;
    bit [7:0] len;
    int total_input_size;
    int ifd0_burst_length;
    begin
      key.get(1);
        begin
             axi_master_stream_ifd0_base_seq.randomize() with {
               sequence_length == 1;
               burst_length == loop_iter * (row+1) ;
             };
             uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifd0_base_seq = \n %s", axi_master_stream_ifd0_base_seq.sprint()), UVM_HIGH);

             axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
        end
      key.put(1);
    end
  endtask

endclass:ai_core_mvm_random_row_col_matrix_multiplication_test

`endif	// __AI_CORE_MVM_RANDOM_ROW_COL_MATRIX_MULTIPLICATION_TEST__
