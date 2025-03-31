// MVM prgmode 1 test does the UTu multiplication with size 9x8 broadcast mode
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_PRGMODE_2_BROADCAST_MODE_TEST__
`define __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_PRGMODE_2_BROADCAST_MODE_TEST__

class ai_core_mvm_single_matrix_multiplication_prgmode_2_broadcast_mode_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_multiplication_prgmode_2_broadcast_mode_test)
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_multiplication_prgmode_2_broadcast_mode_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_single_matrix_multiplication_prgmode_2_broadcast_mode_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("MVM_SINGLE_BROADCAST_MODE_",$sformatf("MVM single matrix multiplication starting"), UVM_LOW)

     
      configure_prg_reg();
      configure_exe_reg();     
      unsigned_exe_prg_enable();
     
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h00A_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h0000_0304_0000_000A;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifdw_base_seq.randomize() with {
         sequence_length == 1;
//         foreach (data[i]) data[i] == {512{1'b1}} ;
         foreach (data[i]) data[i] == {{504{1'b0}},{8{1'b1}}} ;			
         burst_length == 'd1280;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
      axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

      wait_for_prg_status();
     
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_8000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 64'h6800;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


      if(!axi_wr_seq.randomize() with {
        cfg_addr        == 28'h009_1000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h0000_0003_0001_0000;
      }) 
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if(!axi_master_stream_ifd0_base_seq.randomize() with {
        sequence_length == 1;
        //foreach (data[i]) data[i] == {512{1'b1}} ;
        //foreach (data[i]) data[i] == {{504{1'b0}},{8{1'b1}}} ;
        burst_length == 'd15;							    
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);

      wait_for_exe_status();

      if(mvm_if.prgmode == UTu && mvm_if.broadcast_mode ==1) begin
	`uvm_info("PRGMODE",$sformatf("Programming mode set to %s and broadcast is %d", mvm_if.prgmode,mvm_if.broadcast_mode),UVM_LOW)
      end else begin
	`uvm_error("PRG MODE","Mismatch is prgmode") 	   
      end
     
     
      `uvm_info("MVM_SINGLE_BROADCAST_MODE_",$sformatf("MVM single matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_single_matrix_multiplication_prgmode_2_broadcast_mode_test

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_BROADCAST_MODE_BROADCAST_MODE_TEST__
