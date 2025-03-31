`ifndef IAU_SEQ_ITEM
`define IAU_SEQ_ITEM

class iau_seq_item extends uvm_sequence_item;
  `uvm_object_utils(iau_seq_item)
                                                                        
  bit reset_an_i;
  bit irq_o;
  bit [OBS_W-1:0] obs_o;
  bit [CID_W-1:0] cid_i;
  bit [BLOCK_ID_W-1:0] block_id_i;
 
  function new (string name = "");
    super.new (name);
  endfunction

  virtual function iau_seq_item do_clone();
    iau_seq_item item;

    if(!$cast(item, this.clone()))
      `uvm_error(get_full_name(), "Clone failed")

    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    iau_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.reset_an_i = seq_rhs.reset_an_i;
    this.irq_o      = seq_rhs.irq_o;
    this.obs_o      = seq_rhs.obs_o;
    this.cid_i      = seq_rhs.cid_i;
    this.block_id_i = seq_rhs.block_id_i;
  endfunction : do_copy

  virtual function void reset();
    this.reset_an_i = 0; 
    this.irq_o      = 0; 
    this.obs_o      = 0; 
    this.cid_i      = 0; 
    this.block_id_i = 0; 
  endfunction
endclass

`endif

