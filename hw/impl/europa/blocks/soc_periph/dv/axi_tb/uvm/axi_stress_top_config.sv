`ifndef SOC_PERIPH_AXI_STRESS_TOP_CONFIG_SV
`define SOC_PERIPH_AXI_STRESS_TOP_CONFIG_SV


class axi_stress_top_config extends uvm_object;

  virtual svt_axi_if axi_vif;

  svt_axi_system_configuration m_axi_env_cfg;

  // Number of AXI R/W transactions per thread
  int m_transaction_count = 1;

  // Number of concurrent threads per periph
  int m_nb_threads_per_periph = 1;

  // do not register config class with the factory
  extern function new(string name = "");

endclass : axi_stress_top_config


function axi_stress_top_config::new(string name = "");
  super.new(name);
endfunction : new


`endif  // SOC_PERIPH_AXI_STRESS_TOP_CONFIG_SV
