`ifndef TOKEN_AGENT_SEQ_ITEM_SV
`define TOKEN_AGENT_SEQ_ITEM_SV

class token_agent_seq_item extends uvm_sequence_item;
  `uvm_object_utils(token_agent_seq_item)

  //variable that specifies if this sequence item is related with consumer or producer signals
  rand token_agent_info_type_enm m_type_enm;

  //variables that specify the value that is pretended if is the driver, or seen by the monitor on the interface
  rand bit m_tok_value;

  //variable that specify the delay between the posedge of the input and the posedge of the output variable
  rand int m_bv_delay;

  string m_tok_path_name;

  //sanity constraint for m_bv_delay to make sure the delay is not to high
  constraint ct_delay_sanity {
    soft m_bv_delay inside {[0:10]};
  }
  //distribution constraint to make sure the m_bv_delay will have some situations of 0 delay
  constraint ct_delay_dist {
    soft m_bv_delay dist {
      0     := 40,
      [1:10] :/ 60
    };
  }

  function new (string name = "");
    super.new (name);
  endfunction : new

  virtual function token_agent_seq_item do_clone();
    token_agent_seq_item l_item;

    if(!$cast(l_item, this.clone()))
      `uvm_fatal(get_full_name(), "Clone failed")

    return l_item;
  endfunction : do_clone

  virtual function void do_copy(uvm_object rhs);
    token_agent_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.m_type_enm      = seq_rhs.m_type_enm;
    this.m_tok_value     = seq_rhs.m_tok_value;
    this.m_bv_delay      = seq_rhs.m_bv_delay;
    this.m_tok_path_name = seq_rhs.m_tok_path_name;
  endfunction : do_copy

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n---------------------------------------------") };
    s = {s, $sformatf("\n  name       :   %s"   , get_name()        ) };
    s = {s, $sformatf("\n  path name  :   %s"   , m_tok_path_name   ) };
    s = {s, $sformatf("\n  ID         :   0x%0x", get_inst_id()     ) };
    s = {s, $sformatf("\n  m_type_enm :   %s"   , m_type_enm.name() ) };
    s = {s, $sformatf("\n  m_tok_value:   %0d"  , m_tok_value       ) };
    s = {s, $sformatf("\n  m_bv_delay :   %0d"  , m_bv_delay        ) };
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;

  endfunction : convert2string

endclass : token_agent_seq_item

`endif // TOKEN_AGENT_SEQ_ITEM_SV

