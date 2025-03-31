`ifndef SECURE_SPIKE_TOP_CONFIG_SV
`define SECURE_SPIKE_TOP_CONFIG_SV

class spike_top_config extends uvm_object;

  virtual svt_axi_if axi_vif;

  svt_axi_system_configuration m_axi_env_cfg;

  string m_elf;

  // do not register config class with the factory
  extern function new(string name = "");

endclass : spike_top_config


function spike_top_config::new(string name = "");
  super.new(name);
  m_elf = "";
endfunction : new


`endif  // SECURE_SPIKE_TOP_CONFIG_SV
