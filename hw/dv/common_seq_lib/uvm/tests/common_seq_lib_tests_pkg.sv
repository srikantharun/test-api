// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

package common_seq_lib_tests_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import common_seq_lib_uvm_pkg::*;
  `include "../env/common_seq_lib_tb_define.sv"

  `include "test_cfg.svh"

  //Functional tests
  `include "common_seq_lib_base_test.sv"
  `include "common_tasks.svh"
  `include "common_seq_lib_smoke_test.sv"
  `include "common_seq_lib_write_rand_test.sv"
  `include "common_seq_lib_dma_test.sv"
  `include "common_seq_lib_cac_fill_test.sv"
  `include "pipeline_base_test.sv"
  `include "common_seq_lib_exclusive_axi_test.sv"
  `include "common_seq_lib_read_interleave_test.sv"
  
endpackage : common_seq_lib_tests_pkg

