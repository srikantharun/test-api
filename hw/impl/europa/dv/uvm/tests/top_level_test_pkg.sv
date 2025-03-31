package top_level_test_pkg;

  timeunit 1ns; timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvm_sw_ipc_pkg::*;

  parameter int unsigned AICORE_NUMBER = 8;
  parameter int unsigned PVE_NUMBER = 2;

  parameter int unsigned CORE_NUMBER = apu_pkg::CORE_WIDTH + AICORE_NUMBER + (pve_pkg::PVE_N_CLUSTERS * pve_pkg::PVE_CLUSTER_N_CPU * PVE_NUMBER);

  `include "fw_base_test.sv"
  `include "fw_test_uvm_sw_ipc_sanity.sv"
  `include "emmc_test.sv"
endpackage : top_level_test_pkg
