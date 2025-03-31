// MVM basic test-case class
`ifndef __AI_CORE_MVM_POWER_SURGE_TEST__
`define __AI_CORE_MVM_POWER_SURGE_TEST__

class ai_core_mvm_power_surge_test extends ai_core_mvm_random_matrix_multiplication_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_power_surge_test)
      mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h;
      mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
      mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
      mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
      mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;
  // Class constructor
  function new (string name="ai_core_mvm_power_surge_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_power_surge_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

      super.run_phase(phase); 
      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM power surge test starting"), UVM_HIGH)
      #100ns;

      // Power Smooth Dummy Ops = 1 . Number of Banks going active at any clock cycles is not more than one.
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.power_smooth_dummy_ops.set(1'b1);
      mvm_regmodel.m_mvmexe_regmod.dp_ctrl.update(status);
      mvm_power_surge_check_intf.power_smooth_dummy_ops = 1;

      ral_write_data = 64'h000_0001;
      configure_prg_reg;
      prepare_prg_packet_and_send_ifdw;
      wait_for_prg_status;

      prepare_exe_instr;
      configure_exe_reg;
      prepare_exe_packet_and_send_ifd0;
      wait_for_exe_status;
      
      check_irq_status();

      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM power surge test end"), UVM_HIGH)
    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_power_surge_test

`endif	// __AI_CORE_MVM_POWER_SURGE_TEST__
