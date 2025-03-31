// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM ICDF Stimuli Components 
// Owner: yokota

package axi_icdf_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  `include "axi_icdf_scoreboard.svh"
  `include "axi_master_file_sequence.svh"
  `include "axi_stream_master_file_sequence.svh"

endpackage : axi_icdf_pkg
