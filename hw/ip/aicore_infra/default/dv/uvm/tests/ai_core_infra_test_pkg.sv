package ai_core_infra_test_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif


  import aic_common_pkg::*;
  import ai_core_infra_seq_pkg::*;
  import ai_core_infra_uvm_pkg::*;

  `include "../env/ai_core_infra_tb_define.svh"
  `include "cust_svt_axi_master_transaction.svh"

  `include "ai_core_infra_base_test.svh"
  `include "ai_core_infra_axi_rnd_test.sv"

endpackage : ai_core_infra_test_pkg

