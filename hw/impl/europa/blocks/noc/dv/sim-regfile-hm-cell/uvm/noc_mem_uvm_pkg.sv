package noc_mem_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import axe_uvm_resource_allocator_pkg::*;
  import axe_uvm_scoreboard_pkg::*;
  import axe_uvm_numeric_pkg::*;

  `include "noc_mem_env_cfg.svh"
  `include "noc_mem_item.svh"
  `include "noc_mem_sqr.svh"
  `include "noc_mem_drv.svh"
  `include "noc_mem_mon.svh"
  `include "noc_mem_seq_base.svh"
  `include "noc_mem_scoreboard.svh"
  `include "noc_mem_env.svh"
  `include "noc_mem_test_lib.svh"

endpackage : noc_mem_uvm_pkg
