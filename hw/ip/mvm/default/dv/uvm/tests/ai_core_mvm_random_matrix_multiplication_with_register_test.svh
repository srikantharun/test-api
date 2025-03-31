// MVM basic test-case class
`ifndef __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_WITH_REGISTER_TEST__
`define __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_WITH_REGISTER_TEST__

class ai_core_mvm_random_matrix_multiplication_with_register_test extends ai_core_mvm_random_matrix_multiplication_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_random_matrix_multiplication_with_register_test)
      mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h;
      mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
      mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
      mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
      mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;
      bit irq_en; 
  // Class constructor
  function new (string name="ai_core_mvm_random_matrix_multiplication_with_register_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_matrix_multiplication_with_register_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix multiplication starting"), UVM_LOW)
      #100ns;
      ral_write_data = 64'h000_0001;
     if (($test$plusargs("CMDBLK_CTRL_EXE")) ) begin
      uvm_report_info(get_type_name(), $sformatf("CMDBLK_CTRL_EXE desired=0x%0h mirrored=0x%0h", mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.get(), mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.get_mirrored_value()), UVM_LOW);
       mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
       mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
       uvm_report_info(get_type_name(), $sformatf("CMDBLK_CTRL_EXE desired=0x%0h mirrored=0x%0h", mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.get(), mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.get_mirrored_value()), UVM_LOW);
     end
     else if (($test$plusargs("DP_CTRL")) ) begin
       uvm_report_info(get_type_name(), $sformatf("DP_CTRL desired=0x%0h mirrored=0x%0h", mvm_regmodel.m_mvmexe_regmod.dp_ctrl.get(), mvm_regmodel.m_mvmexe_regmod.dp_ctrl.get_mirrored_value()), UVM_LOW);
       randcase
          1: begin
               mvm_regmodel.m_mvmprg_regmod.dp_ctrl.signed_weights.set(!mvm_regmodel.m_mvmprg_regmod.dp_ctrl.signed_weights.get());
               mvm_regmodel.m_mvmexe_regmod.dp_ctrl.signed_inputs.set(!mvm_regmodel.m_mvmexe_regmod.dp_ctrl.signed_inputs.get());
               uvm_report_info(get_type_name(), $sformatf("DP_CTRL signed_weights & signed_inputs"), UVM_LOW);
             end
         1: begin
              mvm_regmodel.m_mvmexe_regmod.dp_ctrl.power_smooth_dummy_ops.set(!mvm_regmodel.m_mvmexe_regmod.dp_ctrl.power_smooth_dummy_ops.get());
              uvm_report_info(get_type_name(), $sformatf("DP_CTRL power_smooth_dummy_ops"), UVM_LOW);
            end
         1: begin
              mvm_regmodel.m_mvmexe_regmod.dp_ctrl.disable_imc_acc_clock_gating.set(!mvm_regmodel.m_mvmexe_regmod.dp_ctrl.disable_imc_acc_clock_gating.get());
              uvm_report_info(get_type_name(), $sformatf("DP_CTRL disable_imc_acc_clock_gating"), UVM_LOW);
            end
         1: begin
              mvm_regmodel.m_mvmexe_regmod.dp_ctrl.dbg_sw_irq.set(!mvm_regmodel.m_mvmexe_regmod.dp_ctrl.dbg_sw_irq.get());
              uvm_report_info(get_type_name(), $sformatf("DP_CTRL dbg_sw_irq"), UVM_LOW);
              irq_en=1;
            end
       endcase
       mvm_regmodel.m_mvmexe_regmod.dp_ctrl.update(status);
       mvm_regmodel.m_mvmprg_regmod.dp_ctrl.update(status);
       uvm_report_info(get_type_name(), $sformatf("DP_CTRL desired=0x%0h mirrored=0x%0h", mvm_regmodel.m_mvmexe_regmod.dp_ctrl.get(), mvm_regmodel.m_mvmexe_regmod.dp_ctrl.get_mirrored_value()), UVM_LOW);
     end
     else if (($test$plusargs("DBG_SCRATCH")) ) begin
       void'(std::randomize(ral_write_data));
       uvm_report_info(get_type_name(), $psprintf("DBG_SCRATCH = %0h", ral_write_data), UVM_LOW);
       mvm_regmodel.m_mvmexe_regmod.dbg_scratch.write(status, ral_write_data);
     end
     else if (($test$plusargs("CMDBLK_CTRL_PRG")) ) begin
      uvm_report_info(get_type_name(), $sformatf("CMDBLK_CTRL_PRG desired=0x%0h mirrored=0x%0h", mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.get(), mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.get_mirrored_value()), UVM_LOW);
       mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
       mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
       uvm_report_info(get_type_name(), $sformatf("CMDBLK_CTRL_PRG desired=0x%0h mirrored=0x%0h", mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.get(), mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.get_mirrored_value()), UVM_LOW);
     end
     
     configure_prg_reg;
     prepare_prg_packet_and_send_ifdw;
     wait_for_prg_status;

     prepare_exe_instr;
     configure_exe_reg;
     prepare_exe_packet_and_send_ifd0;
     wait_for_exe_status;
    
     if(irq_en!=1) begin
       check_irq_status();
     end
      
     `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix multiplication end"), UVM_LOW)

    phase.drop_objection(this);
  endtask


endclass:ai_core_mvm_random_matrix_multiplication_with_register_test

`endif	// __ai_core_mvm_random_matrix_multiplication_with_register_test__
