`ifndef AIC_DMC_AGENT_SV
`define AIC_DMC_AGENT_SV

class aic_ls_agent extends uvm_agent;
  `uvm_component_utils(aic_ls_agent)

  virtual aic_ls_if vif;
  aic_ls_monitor    mon;
  aic_ls_agent_cfg  cfg_h;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if(!uvm_config_db#(virtual aic_ls_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
    end

    if(!uvm_config_db #(aic_ls_agent_cfg)::get(this,"","cfg",cfg_h))begin
       `uvm_fatal(get_full_name(),"Config object missing")
    end

    mon = aic_ls_monitor::type_id::create("mon",this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    mon.vif = vif;
  endfunction
endclass

`endif


