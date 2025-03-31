`ifndef SECURE_SPIKE_TOP_ENV_SV
`define SECURE_SPIKE_TOP_ENV_SV

class spike_top_env extends uvm_env;

  `uvm_component_utils(spike_top_env)

  extern function new(string name, uvm_component parent);

  spike_top_config   m_config;
  svt_axi_system_env m_axi_system_env;

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

  uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg",
                                                    m_config.m_axi_env_cfg);
  uvm_config_db#(virtual svt_axi_if)::set(this, "m_axi_system_env", "vif", m_config.axi_vif);

  m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);
  

endfunction : build_phase


function void spike_top_env::connect_phase(uvm_phase phase);
  `uvm_info(get_type_name(), "In connect_phase", UVM_HIGH)
  m_axi_system_env.set_report_verbosity_level(UVM_NONE);
  m_axi_system_env.master[0].set_report_verbosity_level(UVM_NONE);
  m_axi_system_env.master[1].set_report_verbosity_level(UVM_NONE);

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

`endif  // SECURE_SPIKE_TOP_ENV_SV
