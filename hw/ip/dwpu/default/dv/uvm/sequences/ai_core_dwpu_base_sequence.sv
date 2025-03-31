/**
 * Base sequence used on other dwpu sequences
 */
class ai_core_dwpu_base_sequence extends uvm_sequence;
  // Register
  `uvm_object_utils(ai_core_dwpu_base_sequence)

  uvm_sequence_base m_parent_seq;
  uvm_phase starting_phase_for_curr_seq;

  // Declare p sequencer
  `uvm_declare_p_sequencer(dwpu_axi_virtual_sequencer)

  // Class constructor
  function new (string name = "ai_core_dwpu_base_sequence");
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

endclass:ai_core_dwpu_base_sequence

