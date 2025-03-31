// // MVM random matrix muliplication test prg and broadcast mode
`ifndef __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_PRGMODE_1_TEST__
`define __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_PRGMODE_1_TEST__

class ai_core_mvm_random_matrix_multiplication_prgmode_1_test extends ai_core_mvm_random_matrix_multiplication_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_random_matrix_multiplication_prgmode_1_test)
        
  // Class constructor
  function new (string name="ai_core_mvm_random_matrix_multiplication_prgmode_1_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_matrix_multiplication_base_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);    
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

      if(mvm_if.prgmode == TUu) begin
	`uvm_info("PRGMODE",$sformatf("Programming mode set to %s", mvm_if.prgmode),UVM_LOW)
      end else begin
	`uvm_error("PRG MODE","Mismatch is prgmode") 	   
      end
     
      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix multiplication prgmode 1 end"), UVM_LOW)
    phase.drop_objection(this);
  endtask // run_phase
  
  virtual task prepare_prg_packet_and_send_ifdw;
     if (!mvm_prg_cmd_tb_data_h.randomize with {mvm_prg_cmd_struct.wb_t_pw < 7;
						mvm_prg_cmd_struct.wb_u_pw < 8;
						mvm_prg_cmd_struct.a_t_pw < 4;
						mvm_prg_cmd_struct.a_t_pw + mvm_prg_cmd_struct.wb_t_pw < 4;	
   		                                mvm_prg_cmd_struct.a_s < 4;
						mvm_prg_cmd_struct.extra == 9; // extra fields has the prg mode 1 and broadcast mode 1
						})
        `uvm_fatal("run_phase", "Failed to randomize");
    uvm_report_info(get_type_name(), $psprintf("PRG MODE 1 mvm_prg_cmd_tb_data_h = \n %s", mvm_prg_cmd_tb_data_h.sprint()), UVM_HIGH);
    if (!axi_wr_seq.randomize() with {
      cfg_addr        == MVM_PRG_CMDB_START_ADDR ;
      sequence_length == 'd1;
      burst_size_enum_t == BURST_SIZE_64BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_2;
      cfg_data[0] == 64'h0000_0000_0000_0000;
      cfg_data[1] == mvm_prg_cmd_tb_data_h.mvm_prg_cmd_data;
    })
      `uvm_fatal("run_phase", "Failed to randomize");
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      fork
         begin
           key.get(1);
           send_ifdw_packet;
           key.put(1);
         end
      join_none
  endtask
  
endclass:ai_core_mvm_random_matrix_multiplication_prgmode_1_test

`endif	// __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_PRGMODE_1_TEST__
