`ifndef AI_CORE_CD_AGENT_SV
`define AI_CORE_CD_AGENT_SV

class ai_core_cd_agent extends uvm_agent;
  `uvm_component_utils(ai_core_cd_agent)

  ai_core_cd_monitor mon;
  //ai_core_cd_driver  drv;
  virtual ai_core_cd_if vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = ai_core_cd_monitor::type_id::create("mon",this);

    if(!uvm_config_db#(virtual ai_core_cd_if)::get(this, "", "vif", vif))
      `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    mon.vif = vif;
    //drv.vif = vif;

  endfunction
endclass

`endif


