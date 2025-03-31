// MVM basic test-case class
`ifndef __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_TEST_SW_TEST_MODE__
`define __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_TEST_SW_TEST_MODE___

class ai_core_mvm_random_matrix_multiplication_test_sw_test_mode extends ai_core_mvm_random_matrix_multiplication_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_random_matrix_multiplication_test_sw_test_mode)
      mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h;
      mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
      mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
      mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
      mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;
  // Class constructor
  function new (string name="ai_core_mvm_random_matrix_multiplication_test_sw_test_mode", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_matrix_multiplication_test_sw_test_mode", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    void'(randomize());      
    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

      `uvm_info("MVM_RANDOM_SW_TEST_MODE_TEST",$sformatf("MVM random matrix multiplication starting"), UVM_LOW)
      #100ns;
      ral_write_data = 64'h000_0001;
      configure_dp_ctrl_reg; 

      `uvm_info("MVM_RANDOM_TEST_SW_TEST_MODE",$sformatf("MVM random matrix multiplication end"), UVM_LOW)
    phase.drop_objection(this);
  endtask

   task configure_dp_ctrl_reg;
     int delay;
     fork
	begin
	  void'(std::randomize(delay) with { delay inside {[0:300]};});
          #(delay * 10ns);
          mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, test_mode_data);
          mvm_regmodel.m_mvmprg_regmod.dp_ctrl.write(status, 0);
	end	
     join_none
   endtask        

endclass:ai_core_mvm_random_matrix_multiplication_test_sw_test_mode

`endif	// __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_TEST_SW_TEST_MODE__
