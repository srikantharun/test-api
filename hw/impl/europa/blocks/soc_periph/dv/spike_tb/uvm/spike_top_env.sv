`ifndef SOC_IO_SPIKE_TOP_ENV_SV
`define SOC_IO_SPIKE_TOP_ENV_SV

class spike_top_env extends uvm_env;

  `uvm_component_utils(spike_top_env)

  extern function new(string name, uvm_component parent);

  spike_top_config m_config;
  svt_axi_system_env m_axi_system_env;
  svt_spi_agent m_spi_agents[`SVT_SPI_MAX_NUM_SLAVES];
  spike_top_scoreboard m_top_sb;

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);

endclass : spike_top_env


function spike_top_env::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


function void spike_top_env::build_phase(uvm_phase phase);
  `uvm_info(get_type_name(), "In build_phase", UVM_HIGH)

  if (!uvm_config_db#(spike_top_config)::get(this, "", "config", m_config))
    `uvm_fatal(get_type_name(), "Unable to get spike_top_config")

  // Configure AXI VIP
  uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg",
                                                    m_config.m_axi_env_cfg);
  uvm_config_db#(virtual svt_axi_if)::set(this, "m_axi_system_env", "vif", m_config.axi_vif);

  // Default sequence for axi slave: store/retrieve data in its internal memory
  uvm_config_db#(uvm_object_wrapper)::set(this, "m_axi_system_env.slave*.sequencer.run_phase",
                                          "default_sequence", axi_slave_mem_seq::type_id::get());


  // Configure SPI VIPs
  foreach (m_spi_agents[i]) begin
    automatic string agent_name = $sformatf("spi_agent[%0d]", i);
    automatic svt_spi_agent_configuration spi_agent_cfg = new($sformatf("spi_agent_cfg[%0d]", i));
    spi_agent_cfg.is_master = 0;
    spi_agent_cfg.slave_id = i;
    spi_agent_cfg.spi_feature = m_config.m_spi_agent_shared_cfg.spi_feature;
    spi_agent_cfg.frame_format = m_config.m_spi_agent_shared_cfg.frame_format;
    spi_agent_cfg.spi_if = m_config.m_spi_agent_shared_cfg.spi_if;
    uvm_config_db#(svt_spi_agent_configuration)::set(this, agent_name, "cfg", spi_agent_cfg);
    m_spi_agents[i] = svt_spi_agent::type_id::create($sformatf("spi_agent[%0d]", i), this);
  end

  m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);
  m_top_sb = spike_top_scoreboard::type_id::create("m_top_sb", this);

  // Default sequence for axi slave: store/retrieve data in its internal memory
  uvm_config_db#(uvm_object_wrapper)::set(this, "m_axi_system_env.slave*.sequencer.run_phase",
                                          "default_sequence", axi_slave_mem_seq::type_id::get());

endfunction : build_phase


function void spike_top_env::connect_phase(uvm_phase phase);
  `uvm_info(get_type_name(), "In connect_phase", UVM_HIGH)

  // TODO: Give each agent its own port ?
  foreach (m_spi_agents[i]) begin
    m_spi_agents[i].txrx_mon.rx_xact_observed_port.connect(m_top_sb.analysis_imp_spi_rx);
  end

endfunction : connect_phase


function void spike_top_env::end_of_elaboration_phase(uvm_phase phase);
  uvm_factory factory = uvm_factory::get();
  `uvm_info(get_type_name(),
            "Information printed from spike_top_env::end_of_elaboration_phase method", UVM_MEDIUM)
  `uvm_info(get_type_name(), $sformatf("Verbosity threshold is %d", get_report_verbosity_level()),
            UVM_MEDIUM)
  uvm_top.print_topology();
  factory.print();
endfunction : end_of_elaboration_phase

`endif  // SOC_IO_SPIKE_TOP_ENV_SV
