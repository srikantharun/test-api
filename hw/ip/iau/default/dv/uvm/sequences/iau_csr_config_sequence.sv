`ifndef IAU_CSR_CONFIG_SEQUENCE_SV
`define IAU_CSR_CONFIG_SEQUENCE_SV

class iau_csr_config_sequence extends uvm_sequence;
  // Uvm object Utility macro
  rand bit iau_exec_set; // bit for enabling iau
  //iau_csr.DP_CTRL fields
  rand bit sat_op;
  rand bit signed_op;
  rand bit ignore_segfault;

  //iau_csr.IRQ_EN fields
  rand irq_en_t irq_en;

  bit icdf_enable;

  `uvm_object_utils(iau_csr_config_sequence)

  uvm_sequence_base m_parent_seq;
  uvm_phase starting_phase_for_curr_seq;

   // Declare a p sequencer
  `uvm_declare_p_sequencer(axi_virtual_sequencer)

  constraint exec_set_c {
    soft iau_exec_set == 1;
  }

   // Constraining it to 1, to meet ICDF requirements
  constraint signed_op_c {
    if (icdf_enable) {
      soft signed_op == 1;
      soft sat_op    == 0;
    }
  }

  // Class Constructor
  function new (string name = "iau_csr_config_sequence");
    super.new(name);
  endfunction

  virtual task pre_start();
    super.pre_start();

    m_parent_seq = get_parent_sequence();
    if(m_parent_seq == null) begin
      `uvm_info("pre_start", $sformatf("This is a parent sequence so raise objection"), UVM_HIGH)
      `ifdef SVT_UVM_12_OR_HIGHER
        starting_phase_for_curr_seq = get_starting_phase();
      `else
        starting_phase_for_curr_seq = starting_phase;
      `endif
      if (starting_phase_for_curr_seq != null) begin
        starting_phase_for_curr_seq.raise_objection(this);
      end
    end
    else begin
      `uvm_info("pre_start", $sformatf("This is not a parent sequence so do not raise objection"), UVM_HIGH)
    end
  endtask : pre_start

  virtual task post_start();
    super.post_start();
    if(m_parent_seq == null) begin
      `uvm_info("post_start", $sformatf("This is a parent sequence so drop objection"), UVM_HIGH)
      if (starting_phase_for_curr_seq != null) begin
        starting_phase_for_curr_seq.drop_objection(this);
      end
    end
    else begin
      `uvm_info("post_start", $sformatf("This is not a parent sequence so do not drop objection"), UVM_HIGH)
    end
  endtask : post_start

  virtual task body();
    uvm_status_e status; // uvm status for write and read

    `uvm_info("body", $sformatf("Entering on csr config sequence body..."), UVM_HIGH)
    p_sequencer.regmodel.cmdblk_ctrl.write(status, iau_exec_set);
    //iau_csr.DP_CTRL
    p_sequencer.regmodel.dp_ctrl.write(status, {ignore_segfault,sat_op,signed_op});
    p_sequencer.regmodel.irq_en.write(status, irq_en);
    `uvm_info("body", $sformatf("Finished csr config sequence body..."), UVM_HIGH)
  endtask

endclass


`endif
