
function decoder_env::new(string name="decoder_env", uvm_component parent=null);
  super.new(name, parent);
endfunction: new

function void decoder_env::build_phase (uvm_phase phase);
  if (!uvm_config_db#(svt_axi_system_configuration)::get(this, "", "m_axi_env_cfg", m_axi_env_cfg)) begin
    `uvm_warning(get_name(), "No 'm_axi_env_cfg' user settings, creating a default one with random timings")
    m_axi_env_cfg = svt_axi_system_configuration::type_id::create("m_axi_env_cfg");
    m_axi_env_cfg.num_masters           = 4;
    m_axi_env_cfg.num_slaves            = 0;
    m_axi_env_cfg.system_monitor_enable = 0;
    m_axi_env_cfg.common_clock_mode     = 0;
    m_axi_env_cfg.create_sub_cfgs(m_axi_env_cfg.num_masters,m_axi_env_cfg.num_slaves);
    for (int i=0; i<m_axi_env_cfg.num_masters; i++) begin
      m_axi_env_cfg.master_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      m_axi_env_cfg.master_cfg[i].data_width = CODEC_AXI_DATA_WIDTH;
      m_axi_env_cfg.master_cfg[i].addr_width = CODEC_AXI_ADDR_WIDTH;
      m_axi_env_cfg.master_cfg[i].id_width   = CODEC_AXI_ID_WIDTH;
      m_axi_env_cfg.master_cfg[i].is_active  = 0;
    end
  end
  uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", m_axi_env_cfg);

  if (!uvm_config_db#(svt_apb_system_configuration)::get(this, "", "m_apb_env_cfg", m_apb_env_cfg)) begin
    `uvm_warning(get_name(), "No 'm_apb_env_cfg' user settings, creating a default one with random timings")
    m_apb_env_cfg = svt_apb_system_configuration::type_id::create("m_apb_env_cfg");
    m_apb_env_cfg.pdata_width            = DCD_TARG_CFG_APB_DATA_W;
    m_apb_env_cfg.paddr_width            = DCD_TARG_CFG_APB_ADDR_W+2;
    m_apb_env_cfg.apb4_enable            = 0;
    m_apb_env_cfg.create_sub_cfgs(1);
    m_apb_env_cfg.slave_cfg[0].is_active = 0;
  end
  uvm_config_db#(svt_apb_system_configuration)::set(this, "m_apb_system_env", "cfg", m_apb_env_cfg);

  if (!uvm_config_db#(virtual decoder_if)::get(this, "", "vif", vif)) begin
    `uvm_fatal("NOVIF",  {"Virtual interface must be set for: ", get_full_name(), ".vif"})
  end

  uvm_config_db#(virtual svt_axi_if)::set(this, "m_axi_system_env", "vif", vif.axi_if);
  uvm_config_db#(virtual svt_apb_if)::set(this, "m_apb_system_env", "vif", vif.apb_if);

  m_scoreboard = decoder_scoreboard::type_id::create("m_scoreboard", this);
  m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);
  m_apb_system_env = svt_apb_system_env::type_id::create("m_apb_system_env", this);

  if (uvm_top.get_report_verbosity_level() != UVM_DEBUG) begin
    m_axi_system_env.set_report_verbosity_level_hier(UVM_NONE);
  end
endfunction: build_phase

function void decoder_env::connect_phase (uvm_phase phase);
  m_axi_system_env.master[0].monitor.item_observed_port.connect(m_scoreboard.decoder_mcu_axi_export  );
  m_axi_system_env.master[1].monitor.item_observed_port.connect(m_scoreboard.decoder_core0_axi_export);
  m_axi_system_env.master[2].monitor.item_observed_port.connect(m_scoreboard.decoder_core1_axi_export);
  m_axi_system_env.master[3].monitor.item_observed_port.connect(m_scoreboard.decoder_postproc_axi_export);
  m_apb_system_env.slave[0].monitor.item_observed_port.connect(m_scoreboard.decoder_apb_export);
endfunction: connect_phase


