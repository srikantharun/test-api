`ifndef DMC_ADDR_GEN_AGENT_SV
`define DMC_ADDR_GEN_AGENT_SV

class dmc_addr_gen_agent extends uvm_agent;
  `uvm_component_utils(dmc_addr_gen_agent)

  virtual dmc_addr_gen_if vif;
  dmc_addr_gen_monitor    mon;
  dmc_addr_gen_driver     drv;
  dmc_addr_gen_sequencer  sqr;
  dmc_addr_gen_cfg        cfg_h;
  uvm_event                   m_addr_gen_evt;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if(!uvm_config_db#(virtual dmc_addr_gen_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
    end

    if(!uvm_config_db #(dmc_addr_gen_cfg)::get(this,"","cfg",cfg_h))begin
       `uvm_fatal(get_full_name(),"Config object missing")
    end

    if (cfg_h.is_active == UVM_ACTIVE) begin
      drv = dmc_addr_gen_driver::type_id::create("drv",this);
      sqr = dmc_addr_gen_sequencer::type_id::create("sqr",this);
    end
    mon = dmc_addr_gen_monitor::type_id::create("mon",this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    mon.vif = vif;

    if (cfg_h.is_active == UVM_ACTIVE) begin
      drv.seq_item_port.connect(sqr.seq_item_export);
      drv.vif = vif;
      sqr.vif = vif;
    end
    m_addr_gen_evt =  uvm_event_pool::get_global($sformatf("%s_addr_gen_evt", get_name()));
    mon.m_addr_gen_evt_h = m_addr_gen_evt;
    `uvm_info(get_full_name(), $sformatf("%s_addr_gen_evt created!", get_name()), UVM_LOW)
  endfunction
endclass

`endif


