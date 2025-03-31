`ifndef DPU_CSR_CONFIG_SEQUENCE_SVH
`define DPU_CSR_CONFIG_SEQUENCE_SVH

class dpu_csr_config_sequence extends uvm_sequence; 
  `uvm_object_utils(dpu_csr_config_sequence)
  `uvm_declare_p_sequencer(axi_virtual_sequencer)

  bit dpu_exe              = 1;  
  dpu_irq_reg_t irq_en_reg = 64'hFFFF_FFFF_FFFF_FFFF;
  rand dp_ctrl_reg_t dp_ctrl_reg;

  constraint c_dp_ctrl {
    soft dp_ctrl_reg.dbg_sw_irq         == 0;
    soft dp_ctrl_reg.drop_illegal_instr == 0;
    soft dp_ctrl_reg.skip_illegal_prog  == 0;
    dp_ctrl_reg.unused_27b              == 0;
  }

  function new(string name = "dpu_csr_config_sequence");
    super.new(name);
  endfunction


  virtual task body();
    uvm_status_e status;  // uvm status for write and read
    `uvm_info(get_name(), $sformatf("writing cmdblk_ctrl irq_en: %p", irq_en_reg), UVM_HIGH)
    
    p_sequencer.regmodel.cmdblk_ctrl.write(status, dpu_exe);
    if (status == UVM_NOT_OK)
    `uvm_error(get_type_name(), $sformatf(" writing operation falied for reg %s",
               p_sequencer.regmodel.cmdblk_ctrl.get_full_name()))
    
    p_sequencer.regmodel.dp_ctrl.write(status, dp_ctrl_reg);
    if (status == UVM_NOT_OK)
    `uvm_error(get_type_name(), $sformatf(" writing operation falied for reg %s",
               p_sequencer.regmodel.dp_ctrl.get_full_name()))

    p_sequencer.regmodel.irq_en.write(status, irq_en_reg); 
    if (status == UVM_NOT_OK)
    `uvm_error(get_type_name(), $sformatf(" writing operation falied for reg %s",
               p_sequencer.regmodel.irq_en.get_full_name()))

  endtask

endclass
`endif
