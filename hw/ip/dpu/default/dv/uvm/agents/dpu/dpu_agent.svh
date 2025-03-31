`ifndef DPU_AGENT_SV
`define DPU_AGENT_SV

class dpu_agent extends uvm_agent;
  `uvm_component_utils(dpu_agent)

  dpu_monitor mon;
  virtual dpu_if vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = dpu_monitor::type_id::create("mon",this);

    if(!uvm_config_db#(virtual dpu_if)::get(this, "", "vif", vif))
      `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    mon.vif = vif;
  endfunction
endclass

`endif


