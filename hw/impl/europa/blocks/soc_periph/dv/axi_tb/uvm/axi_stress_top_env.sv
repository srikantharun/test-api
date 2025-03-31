`ifndef SOC_PERIPH_AXI_STRESS_TOP_ENV_SV
`define SOC_PERIPH_AXI_STRESS_TOP_ENV_SV

class axi_stress_top_env extends uvm_env;

  `uvm_component_utils(axi_stress_top_env)

  extern function new(string name, uvm_component parent);

  axi_stress_top_config m_config;
  axi_stress_top_scoreboard m_scoreboard;
  svt_axi_system_env m_axi_system_env;
  svt_apb_system_env m_timers_apb_system_env;
  svt_apb_system_env m_gpio_apb_system_env;
  svt_apb_system_env m_i2c_0_apb_system_env;
  svt_apb_system_env m_i2c_1_apb_system_env;
  svt_apb_system_env m_ssi_apb_system_env;
  svt_apb_system_env m_uart_apb_system_env;
  svt_apb_system_env m_emmc_apb_system_env;

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);

endclass : axi_stress_top_env


function axi_stress_top_env::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


function void axi_stress_top_env::build_phase(uvm_phase phase);
  `uvm_info(get_type_name(), "In build_phase", UVM_HIGH)

  if (!uvm_config_db#(axi_stress_top_config)::get(this, "", "config", m_config))
    `uvm_fatal(get_type_name(), "Unable to get axi_stress_top_config")

  // ---------------------------------------------------------------------------
  // AXI env config
  // ---------------------------------------------------------------------------

  uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg",
                                                    m_config.m_axi_env_cfg);
  uvm_config_db#(virtual svt_axi_if)::set(this, "m_axi_system_env", "vif", m_config.axi_vif);

  m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);
  m_timers_apb_system_env = svt_apb_system_env::type_id::create("m_timers_apb_system_env", this);
  m_gpio_apb_system_env = svt_apb_system_env::type_id::create("m_gpio_apb_system_env", this);
  m_i2c_0_apb_system_env = svt_apb_system_env::type_id::create("m_i2c_0_apb_system_env", this);
  m_i2c_1_apb_system_env = svt_apb_system_env::type_id::create("m_i2c_1_apb_system_env", this);
  m_ssi_apb_system_env = svt_apb_system_env::type_id::create("m_ssi_apb_system_env", this);
  m_uart_apb_system_env = svt_apb_system_env::type_id::create("m_uart_apb_system_env", this);
  m_emmc_apb_system_env = svt_apb_system_env::type_id::create("m_emmc_apb_system_env", this);
  m_scoreboard = axi_stress_top_scoreboard::type_id::create("m_scoreboard", this);
  m_scoreboard.m_config = m_config;

endfunction : build_phase


function void axi_stress_top_env::connect_phase(uvm_phase phase);
  `uvm_info(get_type_name(), "In connect_phase", UVM_HIGH)

  m_axi_system_env.master[0].monitor.item_observed_port.connect(
      m_scoreboard.axi_master_agent_export);
endfunction : connect_phase


function void axi_stress_top_env::end_of_elaboration_phase(uvm_phase phase);
  uvm_factory factory = uvm_factory::get();
  `uvm_info(get_type_name(),
            "Information printed from axi_stress_top_env::end_of_elaboration_phase method",
            UVM_MEDIUM)
  `uvm_info(get_type_name(), $sformatf("Verbosity threshold is %d", get_report_verbosity_level()),
            UVM_MEDIUM)
  uvm_top.print_topology();
  factory.print();

  // Disable apb checks conflicting with Synopsys's fabric
  // UART + TIMERS pstrb are tied to 'hf
  m_timers_apb_system_env.slave[0].monitor.checks.pstrb_low_for_read.set_is_enabled(0);
  m_uart_apb_system_env.slave[0].monitor.checks.pstrb_low_for_read.set_is_enabled(0);

  // Set default mem value to 0
  m_timers_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
  m_gpio_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
  m_i2c_0_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
  m_i2c_1_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
  m_ssi_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
  m_uart_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
  m_emmc_apb_system_env.slave[0].apb_slave_mem.meminit = svt_mem::ZEROES;
endfunction : end_of_elaboration_phase

`endif  // SOC_PERIPH_AXI_STRESS_TOP_ENV_SV
