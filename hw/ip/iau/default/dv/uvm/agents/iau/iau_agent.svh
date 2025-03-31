`ifndef IAU_AGENT_SV
`define IAU_AGENT_SV

class iau_agent extends uvm_agent;
  `uvm_component_utils(iau_agent)

  iau_monitor mon;
  virtual iau_if vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = iau_monitor::type_id::create("mon",this);

    if(!uvm_config_db#(virtual iau_if)::get(this, "", "iau_vif", vif))
      `uvm_fatal(get_full_name(), "Failed to get iau_vif handle from config_db in iau_agent")
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    mon.vif = vif;
  endfunction
endclass

`endif


