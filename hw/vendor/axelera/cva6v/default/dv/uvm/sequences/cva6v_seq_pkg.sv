// *** Axelera AI Confidential ***
//
// Description: CVA6 Sequence Package
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

package cva6v_seq_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import cva6v_env_pkg::*;

  import "DPI-C" function void load_binary_file (input string filename);
  // Sequences
  `include "svt_axi_slv_mem_rsp_seq.sv"
  // add more here
endpackage : cva6v_seq_pkg
