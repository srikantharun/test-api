`ifndef CC_CLK_DIV_AGENT_SEQUENCE_LIBRARY_SW
`define CC_CLK_DIV_AGENT_SEQUENCE_LIBRARY_SV

class cc_clk_div_agent_base_sequence extends uvm_sequence#(cc_clk_div_agent_seq_item);
  `uvm_object_utils(cc_clk_div_agent_base_sequence)

  //variable that specifies the increment to use in the clock divider
  rand bit [aic_common_pkg::AIC_PHASE_ACC_WIDTH-1:0]  m_incr   ;
  rand bit                                    m_enable ;

  constraint c_enable_sanity {
    soft m_enable == 1;
  }

  function new (string name = "");
    super.new (name);
  endfunction : new

  task body();
    cc_clk_div_agent_seq_item clk_div_trans;

    `uvm_info(get_name(), $sformatf("Starting cc_clk_div_agent_base_sequence"), UVM_HIGH)
    `uvm_create(clk_div_trans)
    //randomize transaction
    if(!clk_div_trans.randomize() with {
      m_type_enm == CLK_DIV_DRV;
      m_bv_incr == local::m_incr;
      m_b_enable == local::m_enable;
      m_b_clear == 0;
    }) `uvm_error(get_name, "clk_div_trans randomization error!");
    /** Send the write transaction and wait for the sequence item to be finished */
    `uvm_send(clk_div_trans)

    `uvm_info(get_name(), $sformatf("Finish cc_clk_div_agent_base_sequence"), UVM_HIGH)
  endtask: body
endclass : cc_clk_div_agent_base_sequence

class cc_clk_div_agent_clear_sequence extends uvm_sequence#(cc_clk_div_agent_seq_item);
  `uvm_object_utils(cc_clk_div_agent_clear_sequence)
  
  //variable that specifies the increment to use in the clock divider
  rand bit [aic_common_pkg::AIC_PHASE_ACC_WIDTH-1:0]  m_incr   ;
  rand int m_ns_before_clear;
  rand int m_ns_delay_for_clear;

  constraint c_enable_sanity {
    soft m_ns_before_clear inside {[0:20]};
    soft m_ns_delay_for_clear inside {[1:20]};
  }

  function new (string name = "");
    super.new (name);
  endfunction : new

  task body();
    cc_clk_div_agent_seq_item clk_div_trans;

    `uvm_info(get_name(), $sformatf("Starting cc_clk_div_agent_clear_sequence"), UVM_HIGH)
    //wait some time before clear the clock divider
    #(m_ns_before_clear*1ns);

    `uvm_create(clk_div_trans)
    //randomize transaction
    if(!clk_div_trans.randomize() with {
      m_type_enm  == CLK_DIV_DRV;
      m_bv_incr   == local::m_incr;
      m_b_enable  == 1;
      m_b_clear   == 1;
    }) `uvm_error(get_name, "clk_div_trans randomization error!");
    /** Send the write transaction and wait for the sequence item to be finished */
    `uvm_send(clk_div_trans)
    #(m_ns_delay_for_clear*50ns);
    
    `uvm_create(clk_div_trans)
    //randomize transaction
    if(!clk_div_trans.randomize() with {
      m_type_enm  == CLK_DIV_DRV;
      m_bv_incr   == local::m_incr;
      m_b_enable  == 1;
      m_b_clear   == 0;
    }) `uvm_error(get_name, "clk_div_trans randomization error!");
    /** Send the write transaction and wait for the sequence item to be finished */
    `uvm_send(clk_div_trans)

    `uvm_info(get_name(), $sformatf("Finish cc_clk_div_agent_clear_sequence"), UVM_HIGH)
  endtask: body
endclass : cc_clk_div_agent_clear_sequence

`endif // CC_CLK_DIV_AGENT_SEQUENCE_LIBRARY_SV

