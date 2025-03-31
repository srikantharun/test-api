`ifndef CC_CLK_DIV_AGENT_SEQ_ITEM_SW
`define CC_CLK_DIV_AGENT_SEQ_ITEM_SV

class cc_clk_div_agent_seq_item extends uvm_sequence_item;
  `uvm_object_utils(cc_clk_div_agent_seq_item)

  //variable that specifies if this sequence item is related with consumer or producer signals
  rand cc_clk_div_agent_info_type_enm m_type_enm;

  /** variables that specify the value that is pretended if is the driver, or seen by the monitor on the interface */
  rand bit [aic_common_pkg::AIC_PHASE_ACC_WIDTH-1:0]  m_bv_incr  ;
  rand bit                                    m_b_enable ;
  rand bit                                    m_b_clear  ;
  rand bit                                    m_b_cg_en  ;

  function new (string name = "");
    super.new (name);
  endfunction : new

  virtual function cc_clk_div_agent_seq_item do_clone();
    cc_clk_div_agent_seq_item l_item;

    if(!$cast(l_item, this.clone()))
      `uvm_fatal(get_full_name(), "Clone failed")

    return l_item;
  endfunction : do_clone

  virtual function void do_copy(uvm_object rhs);
    cc_clk_div_agent_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.m_type_enm = seq_rhs.m_type_enm  ;
    this.m_bv_incr  = seq_rhs.m_bv_incr   ;
    this.m_b_enable = seq_rhs.m_b_enable;
    this.m_b_clear  = seq_rhs.m_b_clear ;
    this.m_b_cg_en  = seq_rhs.m_b_cg_en ;
  endfunction : do_copy

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n---------------------------------------------") };
    s = {s, $sformatf("\n  name       :   %s"   , get_name()        ) };
    s = {s, $sformatf("\n  ID         :   0x%0x", get_inst_id()     ) };
    s = {s, $sformatf("\n  m_type_enm :   %s"   , m_type_enm.name() ) };
    s = {s, $sformatf("\n  m_bv_incr  :   %0d"  , m_bv_incr         ) };
    s = {s, $sformatf("\n  m_b_enable :   %0d"  , m_b_enable        ) };
    s = {s, $sformatf("\n  m_b_clear  :   %0d"  , m_b_clear         ) };
    s = {s, $sformatf("\n  m_b_cg_en  :   %0d"  , m_b_cg_en         ) };
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;

  endfunction : convert2string

endclass : cc_clk_div_agent_seq_item

`endif // CC_CLK_DIV_AGENT_SEQ_ITEM_SV

