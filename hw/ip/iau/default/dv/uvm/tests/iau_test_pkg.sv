package iau_test_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import axi_icdf_pkg::*;
  `endif


  import aic_common_pkg::*;
  import iau_pkg::*;

  import token_agent_uvm_pkg::*;
  import iau_common_pkg::*;
  import iau_ral_pkg::*;
  import iau_seq_pkg::*;
  import iau_env_pkg::*;


  `include "iau_base_test.sv"
 
  `include "iau_axi_test_lib.sv"
  `include "iau_ral_base_test.sv"
  `include "iau_ral_hw_rst_test.sv"
  `include "iau_register_test.sv"
  `include "iau_standard_test.sv"
  `include "iau_cmdblk_backpressure_test.sv"
  `include "iau_icdf_test.sv"
  `include "iau_loop_test.sv"
  `include "iau_rfs_test.sv"
  `include "iau_stream_bypass_test.sv"
  `include "iau_concurrency_cmd_prog_test.sv"
  `include "iau_invalid_access_test.sv"
  `include "iau_irq_test.sv"

endpackage : iau_test_pkg

