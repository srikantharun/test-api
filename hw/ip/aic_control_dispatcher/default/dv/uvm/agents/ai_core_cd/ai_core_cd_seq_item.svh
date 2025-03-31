`ifndef AI_CORE_CD_SEQ_ITEM
`define AI_CORE_CD_SEQ_ITEM


class ai_core_cd_seq_item extends uvm_sequence_item;
  `uvm_object_utils(ai_core_cd_seq_item)
 

  bit             reset_n_i;
  bit             irq_o;
  //-//dwpu_irq_t      irq_type;

  function new (string name = "");
    super.new (name);
  endfunction

  virtual function ai_core_cd_seq_item do_clone();
    ai_core_cd_seq_item item;

    if(!$cast(item, this.clone()))
      `uvm_error(get_full_name(), "Clone failed")

    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    ai_core_cd_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.reset_n_i   = seq_rhs.reset_n_i;
    this.irq_o        = seq_rhs.irq_o;
  endfunction : do_copy

  virtual function void reset();
    this.reset_n_i   = 0;
    this.irq_o       = 0;
  endfunction
endclass

`endif

