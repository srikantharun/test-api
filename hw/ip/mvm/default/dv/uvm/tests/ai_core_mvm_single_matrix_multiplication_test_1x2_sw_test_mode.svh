
// MVM basic test-case class
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_TEST_1X2_SW_TEST_MODE___
`define __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_TEST_1X2_SW_TEST_MODE___

class ai_core_mvm_single_matrix_multiplication_test_1x2_sw_test_mode extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_multiplication_test_1x2_sw_test_mode)
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_multiplication_test_1x2_sw_test_mode", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_single_matrix_multiplication_test_1x2_sw_test_mode", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication starting"), UVM_LOW)
      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;
      //test_mode_data   = 64'h 0000_0004;//TM1
      test_mode_data   = 64'h 0000_0002; //TM0
     
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, test_mode_data);
    

      //writing into the exec_en bits in the ex/prg cmd blk control register
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data); //MVMEXE_CSR_BASE_ADDR = 28'h009_0000;
      mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.write(status, ral_write_data); // MVMPRG_CSR_BASE_ADDR = 28'h00A_0000;
   
      //unsigned input data IFD0 and unsigned weights IFDW
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, 0);
      mvm_regmodel.m_mvmprg_regmod.dp_ctrl.write(status, 0);
     
      // writing into the PRG CMDB regidters iwth the matrix for the weight set/row/column offset and also
      //wb_u/t_pw  - A value of 0 maps to an operation on 1 PW, a value of 7 maps to an operation on 8 PWs

      //lt axi writing into the prg_cmdb reg 
      axi_wr_seq.randomize() with {
        cfg_addr        == 28'h00A_1000;    
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        //cfg_data[1] == 64'h0000_0101_0000_0000; //from the spec it is PRG_CDMB reg write  // byte 0 rsvd byte 1 a_s (set id in between 0 to 3) 4 sets of 64x8
	    cfg_data[1] == 64'h0000_0100_0000_0000;                                            // byte 2 a_u_pw byte 3 a_t_pw byte 4 wb_u_pw byte 5 wb_t_pw
				                  //byte 4 and byte 5 is 00 &01 it means rows 1 and column 2 so it is 1x2 matrix 
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      //writing the ifdw data for 2x2 matrix
      axi_master_stream_ifdw_base_seq.randomize() with {
	foreach (data[i]) data[i] == {512{1'b1}} ;	
         sequence_length == 1;
 	 burst_length == 'd128;						
      };
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

      //wait for the status reead to check the register write happen
       wait_for_prg_status();
 
      // writind data into the EXE_CMDB reg
      axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_8000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        //cfg_data[0] == 16'h0900;  // set the offsets for the rectangle pword qcmd spec bits 8&11
				   //0x1200 for the matrix 2x2
        cfg_data[0] == 16'h2000;			   
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      
      //writing into the header and the data in the EXE_CMDB reg
      axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;  // needs to send the header and the data so burst length 2
        cfg_data[0] == 64'h0000_0000_0000_0000;  //byte 6th for by pass operation
        cfg_data[1] == 64'h0000_0002_0001_0000; // * iter 2  //iter length 3
      };

     
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      //writing into ifd0 data 
      axi_master_stream_ifd0_base_seq.randomize() with {
	foreach (data[i]) data[i] == {512{1'b1}} ;		       		
        sequence_length == 1;
        burst_length == 'd2; // 4*512 bits  2x1 now of IFd0 1 * loop iter 2 = ifd0 data 2 now_of_rows* loop_iter = 
      };
      axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);

      wait_for_exe_status();
      
      check_irq_status();


      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_single_matrix_multiplication_test_1x2_sw_test_mode

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_TEST_1X2_SW_TEST_MODE___
