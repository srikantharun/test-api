package axi_stress_top_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  `include "axi_stress_top_config.sv"
  `include "axi_stress_top_scoreboard.sv"
  `include "axi_stress_top_env.sv"

endpackage : axi_stress_top_pkg
