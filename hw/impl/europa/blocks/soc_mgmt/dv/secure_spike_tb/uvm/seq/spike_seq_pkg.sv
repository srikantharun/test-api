package spike_seq_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  `include "spike_axi_single_read_seq.sv"
  `include "spike_axi_single_write_seq.sv"
  `include "axi_slave_mem_seq.sv"

endpackage : spike_seq_pkg
