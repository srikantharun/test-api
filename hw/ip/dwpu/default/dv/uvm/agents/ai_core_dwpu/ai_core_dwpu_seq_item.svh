`ifndef AI_CORE_DWPU_SEQ_ITEM
`define AI_CORE_DWPU_SEQ_ITEM


class ai_core_dwpu_seq_item extends uvm_sequence_item;
  `uvm_object_utils(ai_core_dwpu_seq_item)
 

  bit             reset_an_i;
  bit             irq_o;
  dwpu_irq_t      irq_type;
  bit [OBS_W-1:0] obs_o;
  bit [CID_W-1:0] cid_i;
  bit             trace_vld_o;

  function new (string name = "");
    super.new (name);
  endfunction

  virtual function ai_core_dwpu_seq_item do_clone();
    ai_core_dwpu_seq_item item;

    if(!$cast(item, this.clone()))
      `uvm_error(get_full_name(), "Clone failed")

    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    ai_core_dwpu_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.reset_an_i   = seq_rhs.reset_an_i;
    this.irq_o        = seq_rhs.irq_o;
    this.obs_o        = seq_rhs.obs_o;
    this.cid_i        = seq_rhs.cid_i;
    this.trace_vld_o  = seq_rhs.trace_vld_o;
  endfunction : do_copy

  virtual function void reset();
    this.reset_an_i   = 0;
    this.irq_o        = 0;
    this.obs_o        = 0;
    this.cid_i        = 0;
    this.trace_vld_o  = 0;
  endfunction
endclass

`endif

