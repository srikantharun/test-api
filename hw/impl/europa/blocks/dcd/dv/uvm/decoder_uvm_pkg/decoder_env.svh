
class decoder_env extends uvm_env;

  `uvm_component_utils(decoder_env)

  virtual interface decoder_if vif;

  svt_axi_system_env           m_axi_system_env;
  svt_axi_system_configuration m_axi_env_cfg;
  svt_apb_system_env           m_apb_system_env;
  svt_apb_system_configuration m_apb_env_cfg;
  decoder_scoreboard           m_scoreboard;

  extern function new(string name="decoder_env", uvm_component parent=null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass: decoder_env
