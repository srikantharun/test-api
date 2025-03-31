// MVM basic test-case class
`ifndef __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_RAND_LOOP_LEN_TEST__
`define __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_RAND_LOOP_LEN_TEST__

class ai_core_mvm_single_matrix_multiplication_rand_loop_len_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_single_matrix_multiplication_rand_loop_len_test)
  rand bit [15:0] rand_loop_len;
   

  constraint exe_loop_len_c { rand_loop_len dist {
                            // Small bins with higher probability
                            1  := 10, 2  := 10, 3  := 10, 4  := 10, 5  := 10,
                            // Medium bins with moderate probability
                            122 := 5, 123 := 5, 124 := 5,
                            // Large bins with moderate probability
                            251 := 5, 252 := 5, 253 := 5, 254 := 5, 255 := 5,
                            // Other ranges with evenly distributed probability
                            [6:10]    := 3,   // Small range
                            [11:50]   := 2,   // Medium range
                            [51:100]  := 2,   // Larger range
                            [100:121] := 2,   // Larger range before medium
                            [125:150] := 2,   // After medium range
                            [151:200] := 2,   // Next large range
                            [201:250] := 2    // Range before large bins
                            }; }
  // Class constructor
  function new (string name="ai_core_mvm_single_matrix_multiplication_rand_loop_len_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_signed_single_matrix_multiplication_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
    `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication starting"), UVM_LOW)

    for(int i=0; i<10; i++) begin
      `uvm_info("MVM_SINGLE_TEST",$sformatf("value of i= %d",i), UVM_LOW)
      void'(randomize());
      rand_loop_len_cover;	
    end // 

    `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask

  task rand_loop_len_cover;
      
    configure_exe_reg();
    configure_prg_reg();
        
    axi_wr_seq.randomize() with {
      cfg_addr        == 28'h00A_1000;
      sequence_length == 'd1;
      burst_size_enum_t == BURST_SIZE_64BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_2;
      cfg_data[0] == 64'h0000_0000_0000_0000;
      cfg_data[1] == 64'h0000_0101_0000_0000;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_master_stream_ifdw_base_seq.randomize() with {
       sequence_length == 1;
       foreach (data[i]) data[i] == {512{1'b1}} ;
       burst_length == 'd256;
    };
    uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_LOW);
    axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);

    wait_for_prg_status();

    configure_exe_instr_cmd(.loop_len(rand_loop_len));
    
    wait_for_exe_status();

    check_irq_status();
  endtask //  

  task configure_exe_instr_cmd(logic[15:0] loop_len);
 
    `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication loop length is %d",loop_len), UVM_HIGH)
    for (int j=1; j<=loop_len; j++) begin
      `uvm_info("MVM_SINGLE_TEST",$sformatf("MVM single matrix multiplication i is %d",j), UVM_HIGH)
    
      axi_wr_seq.randomize() with {
      cfg_addr        == 28'h009_8000 + (j-1)*2;
      sequence_length == 'd1;
      burst_size_enum_t == BURST_SIZE_16BIT;
      burst_type_enum_t == FIXED;
      burst_lenght_enum_t == BURST_LENGTH_1;
      cfg_data[0] == 64'h2200;
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
    end
 
    axi_wr_seq.randomize() with {
    cfg_addr        == 28'h009_1000;
    sequence_length == 'd1;
    burst_size_enum_t == BURST_SIZE_64BIT;
    burst_type_enum_t == INCR;
    burst_lenght_enum_t == BURST_LENGTH_2;
    cfg_data[0] == 64'h0000_0000_0000_0000;
    cfg_data[1] == {8'b0, 24'b11, loop_len, 16'b0};
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_master_stream_ifd0_base_seq.randomize() with {
      sequence_length == 1;
      burst_length == loop_len*3*2;  //(loop_iter*row*loop_len)
      //foreach (data[i]) data[i] == {512{1'b1}} ;
    };
    axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
 
   
  endtask //   

endclass:ai_core_mvm_single_matrix_multiplication_rand_loop_len_test

`endif	// __AI_CORE_MVM_SINGLE_MATRIX_MULTIPLICATION_TEST__
