// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: CVA6 Env Package
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>
// CVA6V UVM Env package

package cva6v_env_pkg;

//   timeunit 1ns;
//   timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
    import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  // Environment configuration and environment
  `include "cva6v_axi_system_cfg.sv"
  `include "cva6v_env_cfg.sv"
  `include "cva6v_env.sv"
endpackage : cva6v_env_pkg
