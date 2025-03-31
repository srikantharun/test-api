package ai_core_cd_test_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    //-//import axi_icdf_pkg::*;
  `endif

  import aic_common_pkg::*;
  import aic_cd_pkg::*;
  import common_seq_lib_uvm_pkg::*;
  import aic_cd_csr_ral_pkg::*;
  import ai_core_cd_seq_pkg::*;
  import ai_core_cd_env_pkg::*;
  import axe_uvm_resource_allocator_pkg::*;
  import ai_core_cd_command_pkg::*;
  import ai_core_cd_ref_models_pkg::*;
  //-//import token_agent_uvm_pkg::*;
  //-//import ai_core_dwpu_agent_pkg::*;
  import ai_core_cd_common_pkg::*;
  import token_agent_uvm_pkg::*;  //remove this package after debug

  typedef string string_queue_t [$];
  typedef int int_index_arr_t[int];

  //include macros to be used in cmd sequence
  //-//`include "ai_core_dp_cmd_gen_cmdb_macros.svh"

  //RAL and memory tests
  `include "ai_core_cd_base_test.sv"
  `include "ai_core_cd_instr_tms_smoke_test.sv"
  `include "ai_core_cd_instr_tkn_smoke_test.sv"
  `include "ai_core_cd_instr_cmd_smoke_test.sv"
  `include "ai_core_cd_instr_prg_smoke_test.sv"
  `include "ai_core_cd_instr_prg_smoke_light_test.sv"
  //-//`include "ai_core_dwpu_ral_test.sv"

  //Functional tests
  //-//`include "ai_core_cd_standard_test.sv"
   
endpackage : ai_core_cd_test_pkg
