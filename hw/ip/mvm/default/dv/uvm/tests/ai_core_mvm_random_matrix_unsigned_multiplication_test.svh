// MVM basic test-case class
`ifndef __AI_CORE_MVM_RANDOM_MATRIX_UNSIGNED_MULTIPLICATION_TEST__
`define __AI_CORE_MVM_RANDOM_MATRIX_UNSIGNED_MULTIPLICATION_TEST__

class ai_core_mvm_random_matrix_unsigned_multiplication_test extends ai_core_mvm_random_matrix_multiplication_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_random_matrix_unsigned_multiplication_test)
   int mvm_iterations;
   
  // Class constructor
  function new (string name="ai_core_mvm_random_matrix_unsigned_multiplication_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_matrix_unsigned_multiplication_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
     
      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix unsigned multiplication starting"), UVM_HIGH)
     if(!$value$plusargs("MVM_ITERATIONS=%0d", mvm_iterations)) mvm_iterations = 5;

     //writing into the dp ctrl exe/prg reg to enable the unsigned multiplication
     unsigned_exe_prg_enable();
     
     for(int i=0; i< mvm_iterations; i++) begin  

	`uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix unsigned multiplication starting %d", i), UVM_HIGH)    
	 rand_matrix_multi_seq;
	
     end // for (int i=0; i< 5; i++)
     

      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix unsigned multiplication end"), UVM_HIGH)
    phase.drop_objection(this);
  endtask

  
   virtual task rand_matrix_multi_seq;
   
      void'(randomize());

      #100ns;
      ral_write_data = 64'h000_0001;
      configure_prg_reg;
      repeat(1) begin
       prepare_prg_packet_and_send_ifdw;
      end
       wait_for_prg_status;

      repeat(1) begin
        prepare_exe_instr;
        configure_exe_reg;
        prepare_exe_packet_and_send_ifd0;
        wait_for_exe_status;
      end
      
      check_irq_status();

   endtask //
     
endclass:ai_core_mvm_random_matrix_unsigned_multiplication_test

`endif	// __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_ITER_TEST__
