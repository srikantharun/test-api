package axi_stress_top_seq_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import axe_uvm_resource_allocator_pkg::*;

  `include "axi_address_chunk_stress_seq.sv"
  `include "axi_range_stress_seq.sv"
endpackage
