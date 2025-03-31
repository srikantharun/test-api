
package ai_core_cd_seq_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif

  
  //-//import dwpu_pkg::*;
  import aic_common_pkg::*;
  //-//import dwpu_csr_ral_pkg::*;
  import ai_core_cd_common_pkg::*;
  import ai_core_cd_env_pkg::*;
  
  `define CLK_PERIOD_PS 1250

  localparam AXI_TRANSACTION_BURST_SIZE_8  = 0;
  localparam AXI_TRANSACTION_BURST_SIZE_16 = 1;
  localparam AXI_TRANSACTION_BURST_SIZE_32 = 2;
  localparam AXI_TRANSACTION_BURST_SIZE_64 = 3;
  localparam AXI_TRANSACTION_BURST_FIXED   = 0;
  localparam AXI_TRANSACTION_BURST_INCR    = 1;
  localparam AXI_TRANSACTION_BURST_WRAP    = 2;
  localparam AXI_OKAY_RESPONSE             = 0;
  localparam AXI_EXOKAY_RESPONSE           = 1;
  localparam AXI_SLVERR_RESPONSE           = 2;
  localparam AXI_DECERR_RESPONSE           = 3;
  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************
  typedef enum bit [3:0] {
    BURST_SIZE_8BIT    = AXI_TRANSACTION_BURST_SIZE_8,
    BURST_SIZE_16BIT   = AXI_TRANSACTION_BURST_SIZE_16,
    BURST_SIZE_32BIT   = AXI_TRANSACTION_BURST_SIZE_32,
    BURST_SIZE_64BIT   = AXI_TRANSACTION_BURST_SIZE_64
  } burst_size_t;

  typedef enum bit[1:0]{
    FIXED = AXI_TRANSACTION_BURST_FIXED,
    INCR =  AXI_TRANSACTION_BURST_INCR,
    WRAP =  AXI_TRANSACTION_BURST_WRAP
  } burst_type_t;

  typedef enum bit[5:0]{
    BURST_LENGTH_1 = 1,
    BURST_LENGTH_2 = 2,
    BURST_LENGTH_4 = 4,
    BURST_LENGTH_8 = 8,
    BURST_LENGTH_16 = 16
  } burst_length_t;

  typedef enum bit [1:0] {
    OKAY    = AXI_OKAY_RESPONSE,
    EXOKAY  = AXI_EXOKAY_RESPONSE,
    SLVERR =  AXI_SLVERR_RESPONSE,
    DECERR  = AXI_DECERR_RESPONSE
  } resp_type_t;

  //include utils macros to be used in program sequence
  //-//`include "ai_core_dp_cmd_gen_utils_macros.svh"

  //-//`include "cust_svt_axi_master_transaction.sv"
  // Sequences
  //-//`include "axi_master_random_discrete_virtual_sequence.sv"
  `include "ai_core_cd_axi_slave_mem_response_sequence.sv"  //ToDO: remove these after we make the common_seq_lib_uvm_pkg sequences work with the test
  `include "ai_core_cd_axi_simple_reset_sequence.sv"        //ToDO: remove these after we make the common_seq_lib_uvm_pkg sequences work with the test
  //-//`include "axi_null_virtual_sequence.sv"
  //-//`include "axi_master_directed_sequence.sv"
  //-//`include "axi_master_random_discrete_sequence.sv"
  //-//`include "axi_master_read_sequence.sv"
  //-//`include "axi_master_write_sequence.sv"
  //-//`include "axi_prog_random_sequence.sv"
  //-//`include "ai_core_dwpu_base_sequence.sv"
  //-//`include "ai_core_dwpu_cmd_sequence.sv"
  //-//`include "ai_core_dwpu_prg_sequence.sv"
  //-//`include "ai_core_dwpu_csr_sequence.sv"
  //-//`include "ai_core_dwpu_stream_sequence.sv"
  //-//`include "ai_core_dwpu_not_addressable_csr_sequence.sv"
  //-//`include "ai_core_dwpu_not_addressable_prog_sequence.sv"
  //-//`include "ai_core_dwpu_initialize_prog_sequence.sv"
  //-//`include "ai_core_dwpu_small_random_prog_sequence.sv"
  //-//`include "ai_core_dwpu_concurrency_cmd_prog_sequence.sv"

  //`include "ai_core_dwpu_seq_library.sv"

endpackage : ai_core_cd_seq_pkg

