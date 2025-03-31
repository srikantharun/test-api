`ifndef CC_CLK_DIV_AGENT_DRIVER_SV
`define CC_CLK_DIV_AGENT_DRIVER_SV

class cc_clk_div_agent_driver extends uvm_driver#(cc_clk_div_agent_seq_item);
  `uvm_component_utils(cc_clk_div_agent_driver)

  //declare clock divider agent configuration
  cc_clk_div_agent_config m_cfg;

  //declare interface
  virtual cc_clk_div_agent_if m_vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if ( ! uvm_config_db#( cc_clk_div_agent_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "cfg" ), .value( m_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
  endfunction

  virtual task reset_phase (uvm_phase phase);
    m_vif.drv.incr <= m_cfg.m_bv_incr;
    m_vif.drv.enable <= m_cfg.m_b_enable;
    m_vif.drv.clear <= 0;
  endtask : reset_phase

  virtual task drive_clock_div(cc_clk_div_agent_seq_item a_req);
    `uvm_info(get_full_name(), $sformatf("Start driving request %s", a_req.convert2string()), UVM_HIGH)
    @(m_vif.drv);
    m_vif.drv.incr <= a_req.m_bv_incr;
    m_vif.drv.enable <= a_req.m_b_enable;
    m_vif.drv.clear <= a_req.m_b_clear;
    `uvm_info(get_full_name(), $sformatf("Finish driving request"), UVM_HIGH)
  endtask : drive_clock_div

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info(get_full_name(), $sformatf("received request %s", req.convert2string()), UVM_HIGH)
        //implement the request
        drive_clock_div(req);
        //send to the upper layer the information that this req has finished
        seq_item_port.item_done();
      end
    join
  endtask
endclass

`endif // CC_CLK_DIV_AGENT_DRIVER_SV


