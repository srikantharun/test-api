`ifndef GUARD_AI_CORE_INFRA_ENV_SV
`define GUARD_AI_CORE_INFRA_ENV_SV

// AI_CORE_INFRA environment class
class ai_core_infra_env extends uvm_env;

  `uvm_component_utils(ai_core_infra_env)

  svt_axi_system_env axi_system_env;
  axi_virtual_sequencer sequencer;

  cust_svt_axi_system_configuration cfg;

  ai_core_infra_uvm_scoreboard ai_core_infra_scoreboard;


  function new (string name="ai_core_infra_env", uvm_component parent=null);
    super.new (name, parent);
  endfunction:new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
    uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cfg);

    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);

    ai_core_infra_scoreboard = ai_core_infra_uvm_scoreboard::type_id::create("ai_core_infra_scoreboard", this);
    
  endfunction:build_phase


  function void connect_phase(uvm_phase phase);
    for (int i = 0; i < `MST_NUM; i++)
      axi_system_env.master[i].monitor.item_observed_port.connect(ai_core_infra_scoreboard.init_reference_data_export[i]);

    for (int i = 0; i < `SLV_NUM; i++)
      axi_system_env.slave[i].monitor.item_observed_port.connect (ai_core_infra_scoreboard.targ_actual_data_export[i]);
  endfunction:connect_phase

endclass

`endif // GUARD_AI_CORE_INFRA_ENV_SV
