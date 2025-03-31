// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: CVA6 Env Package
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>
// CVA6V UVM Env Config

`ifndef GUARD_CVA6V_ENV_CFG_SV
`define GUARD_CVA6V_ENV_CFG_SV

// AI CORE LS environment configuration class
class cva6v_env_cfg extends uvm_object;

  `uvm_object_utils(cva6v_env_cfg)

  rand bit m_svt_axi_vip_en;  // Synopsys AXI vip
  rand bit m_cva6_axi_vip_en; //open-source AXI vip

  constraint C_AXI_VIP_DEFAULT {
    m_svt_axi_vip_en  == 1;
    m_cva6_axi_vip_en == 0;
  }

  function new(string name = "cva6v_env_cfg");
    super.new(name);
  endfunction : new


  virtual function string convert2string();
    string s = super.convert2string();
    // put code here
    return s;
  endfunction : convert2string
endclass : cva6v_env_cfg

`endif  // GUARD_AI_CORE_LS_ENV_CFG_SV
