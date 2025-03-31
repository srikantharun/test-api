`ifndef SOC_IO_SPIKE_TOP_TEST_PKG_SV
`define SOC_IO_SPIKE_TOP_TEST_PKG_SV

package spike_top_test_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import spike_top_pkg::*;
  import spike_seq_pkg::*;
  import uvm_sw_ipc_pkg::*;
  import sd_slot_pkg::*;
  import sd_card_pkg::*;

  `include "spike_dpi_export.sv"
  `include "spike_top_test.sv"
  `include "uart_test.sv"
  `include "timer_test.sv"
  `include "fw_test_uvm_sw_ipc_sanity.sv"
  `include "emmc_test.sv"

endpackage : spike_top_test_pkg

`endif  // SOC_IO_SPIKE_TOP_TEST_PKG_SV
