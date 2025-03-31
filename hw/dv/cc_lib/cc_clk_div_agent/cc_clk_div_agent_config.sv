`ifndef CC_CLK_DIV_AGENT_CONFIG_SV
`define CC_CLK_DIV_AGENT_CONFIG_SV

/** Configuration object to token agent */
class cc_clk_div_agent_config extends uvm_object;
  `uvm_object_utils(cc_clk_div_agent_config)

  /** variable to specify if the agent is active or not (by default is active) */
  bit m_b_active = 1;
  /** variable to specify the divider increment */
  rand bit [aic_common_pkg::AIC_PHASE_ACC_WIDTH-1:0] m_bv_incr;
  rand bit                                   m_b_enable ;

  constraint c_incr_sanity {
    //make a soft constrain to be 0 or the higher values (11 until maximum) to make the testcases to run faster
    soft m_bv_incr inside {0, [11 : $]};
  }

  function new (string name = "cc_clk_div_agent_config");
    super.new (name);
  endfunction

  virtual function void do_copy(uvm_object rhs);
    cc_clk_div_agent_config seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.m_b_active = seq_rhs.m_b_active ;
    this.m_bv_incr  = seq_rhs.m_bv_incr   ;
    this.m_b_enable = seq_rhs.m_b_enable;
  endfunction : do_copy

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n---------------------------------------------") };
    s = {s, $sformatf("\n  name       :   %s"   , get_name()        ) };
    s = {s, $sformatf("\n  ID         :   0x%0x", get_inst_id()     ) };
    s = {s, $sformatf("\n  m_b_active :   %0d"  , m_b_active        ) };
    s = {s, $sformatf("\n  m_bv_incr  :   %0d"  , m_bv_incr         ) };
    s = {s, $sformatf("\n  m_b_enable :   %0d"  , m_b_enable        ) };
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;

  endfunction : convert2string
endclass

`endif // CC_CLK_DIV_AGENT_CONFIG_SV


