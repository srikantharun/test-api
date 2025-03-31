`ifndef SOC_IO_SPIKE_TOP_CONFIG_SV
`define SOC_IO_SPIKE_TOP_CONFIG_SV

class spike_top_config extends uvm_object;

  virtual svt_axi_if axi_vif;
  virtual timer_if timer_vif;
  virtual sd_4v00_if sd_vif;
  virtual uhsii_link_phy16_if uhsii_vif;
  virtual i2c_master_if i2c0_master_vif;
  virtual i2c_master_if i2c1_master_vif;

  svt_axi_system_configuration m_axi_env_cfg;
  svt_spi_agent_configuration m_spi_agent_shared_cfg;

  string m_elf;
  string m_emmc_slave_memfile;

  // do not register config class with the factory
  extern function new(string name = "");

endclass : spike_top_config


function spike_top_config::new(string name = "");
  super.new(name);
  m_elf = "";
endfunction : new


`endif  // SOC_IO_SPIKE_TOP_CONFIG_SV
