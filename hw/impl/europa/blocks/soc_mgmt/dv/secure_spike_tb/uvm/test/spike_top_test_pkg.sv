`ifndef SECURE_SPIKE_TOP_TEST_PKG_SV
`define SECURE_SPIKE_TOP_TEST_PKG_SV

package spike_top_test_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import spike_top_pkg::*;
  import spike_seq_pkg::*;
  import uvm_sw_ipc_pkg::*;

  `include "spike_dpi_export.sv"
  `include "spike_top_test.sv"
  `include "fw_test_uvm_sw_ipc_sanity.sv"

endpackage : spike_top_test_pkg

`endif  // SECURE_SPIKE_TOP_TEST_PKG_SV
