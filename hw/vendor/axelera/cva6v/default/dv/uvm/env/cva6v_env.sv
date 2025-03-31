// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: CVA6 Env Package
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>
// CVA6V UVM Env

`ifndef GUARD_CVA6V_ENV_SV
`define GUARD_CVA6V_ENV_SV


// AI CORE LS environment class
class cva6v_env extends uvm_env;

  `uvm_component_utils(cva6v_env)

  cva6v_env_cfg         m_env_cfg;
  svt_axi_system_env    m_axi_system_env;
  cva6v_axi_system_cfg  m_axi_sys_cfg;

  function new(string name = "cva6v_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (m_env_cfg == null) begin
      if (!uvm_config_db#(cva6v_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg))  begin
        `uvm_error("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
      end
    end

    if (m_env_cfg.m_svt_axi_vip_en==1) begin
      if (uvm_config_db#(cva6v_axi_system_cfg)::get(this, "", "cfg", m_axi_sys_cfg)) begin
        uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", m_axi_sys_cfg);
      end  else begin
        // No configuration passed from test
        m_axi_sys_cfg = cva6v_axi_system_cfg::type_id::create("m_axi_sys_cfg");
        uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", m_axi_sys_cfg);
      end
      m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);
    end

    `uvm_info(get_name(), "Exiting build_phase...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info(get_name, "Entered connect_phase...", UVM_LOW)
  endfunction : connect_phase

endclass : cva6v_env

`endif  // GUARD_AI_CORE_LS_ENV_SV
