
  `ifndef ACD_M_AXI_ID_WIDTH
    //`define ACD_M_AXI_ID_WIDTH 7
    `define ACD_M_AXI_ID_WIDTH 6
  `endif
  `ifndef ACD_M_AXI_ADDR_WIDTH
    `define ACD_M_AXI_ADDR_WIDTH aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH
  `endif
  `ifndef ACD_M_AXI_DATA_WIDTH
    `define ACD_M_AXI_DATA_WIDTH aic_common_pkg::AIC_LT_AXI_DATA_WIDTH
  `endif
  `ifndef ACD_S_AXI_ID_WIDTH
    //`define ACD_S_AXI_ID_WIDTH 1
    `define ACD_S_AXI_ID_WIDTH 7
  `endif
  `ifndef ACD_S_AXI_ADDR_WIDTH
    `define ACD_S_AXI_ADDR_WIDTH aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH
  `endif
  `ifndef ACD_S_AXI_DATA_WIDTH
    `define ACD_S_AXI_DATA_WIDTH aic_common_pkg::AIC_LT_AXI_DATA_WIDTH_WIDTH
  `endif


package ai_core_cd_common_pkg;

  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import uvm_pkg::*;
  import aic_cd_defaults_pkg::*;
  

  typedef struct packed {
    bit[64-1:0] addr;  
    bit[64-1:0] range_base;
    bit[64-1:0] range_top;
    int command_idx;
    int instr_idx;
  } mem_access_st;

  typedef struct packed {
    int tms_id;
    int command_idx;
    int instr_idx;
  } timestamp_t;

  typedef byte byte_arr_t[];


  // Class : axe_uvm_resource_allocator
  class general_q_manipulator #(type T) extends uvm_object;

    typedef general_q_manipulator #(T) this_t;
    `uvm_object_param_utils(this_t)

    T                            q[$];

    function new (string name="");
        super.new(name);
    endfunction : new


    function void print_q_contents(T arg_q[$], string q_name);
      `uvm_info("GQ_Man",$sformatf("---------------------------------------------------"),UVM_LOW)
      `uvm_info("GQ_Man",$sformatf("----------    %0s    ----------",q_name),UVM_LOW)
      `uvm_info("GQ_Man",$sformatf("---------------------------------------------------"),UVM_LOW)
      foreach (arg_q[i])
        `uvm_info("GQ_Man",$sformatf("--- %0s[%0d] = %0p", q_name, i, arg_q[i]),UVM_LOW)
    endfunction : print_q_contents


    function void check_q_is_empty(T arg_q[$], string q_name, fatal=0);
      if (arg_q.size()) begin
        if (fatal) begin
          print_q_contents(arg_q, q_name);
          `uvm_fatal("GQ_Man",$sformatf("QUEUE IS NOT EMPTY AT EOT. %0s.size()=%0d", q_name, arg_q.size()))
        end
        else begin
          print_q_contents(arg_q, q_name);
          `uvm_error("GQ_Man",$sformatf("QUEUE IS NOT EMPTY AT EOT. %0s.size()=%0d", q_name, arg_q.size()))
        end
      end 
    endfunction : check_q_is_empty

  endclass : general_q_manipulator


  //-//import dwpu_pkg::*;
  //-//import dwpu_csr_ral_pkg::*;

  //Defines///////////////////////////
  //localparam AXI_ID_WIDTH                       = 7;
  //localparam AXI_LT_LOCAL_ADDR_WIDTH            = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  //localparam AXI_LT_ADDR_WIDTH                  = aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH;
  //localparam AXI_LT_DATA_WIDTH                  = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  //-//localparam AXI_STREAM_IFD0_DATA_WIDTH         = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;
  localparam AXI_STREAM_IAU_DATA_WIDTH          = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH;
  //-//localparam DWPU_INSTR_NUM_ROWS                = int'($ceil(real'($bits(dwpu_pkg::dwpu_dp_command_t)) / real'(AXI_LT_DATA_WIDTH)));
  //-//localparam DWPU_INSTR_BYTES                   = DWPU_INSTR_NUM_ROWS * 8;
  //-//localparam INSTR_MEM_DEPTH                    = 1024;
  //-//localparam DWPU_IN_WORD_DW                    = AXI_STREAM_IFD0_DATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  //-//localparam DWPU_OUT_WORD_DW                   = AXI_STREAM_IAU_DATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  //-//localparam EXTEND_LEN                         = DWPU_OUT_WORD_DW - DWPU_IN_WORD_DW;
  //localparam ACD_CSR_ST_ADDR                         = aic_addr_map_pkg::AIC_LOC_D_ACD_REGION_ST_ADDR[dwpu_pkg::CSR];
  //localparam ACD_CSR_ST_ADDR                         = aic_addr_map_pkg::AIC_LOC_CFG_ACD_CSR_ST_ADDR;  //ToDO: ask Wolfgang if aic_addr_map_pkg is not needed to import common start/end reg ADDRESSES from EUROPA PROJECT
  ///home/projects_2/workspace/gbratu/europa_aic_cd/europa/hw/impl/europa/asic/rtl/pkg/aipu_addr_map_pkg.sv:    parameter logic [39:0] AICORE_0_CONFIGURATION_CONTROL_ACD_CSR_ST_ADDR = 'h000011000000;
  localparam ACD_CSR_ST_ADDR                         = 'h000011000000;  //ToDO: defined static value until above package import ToDO/OPEN is resolved
  localparam ACD_CMD_ST_ADDR                         = ACD_CSR_ST_ADDR + 'h000000010000;
  //-//localparam DWPU_CSR_END_ADDR                  = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR[dwpu_pkg::CSR];
  //-//localparam DWPU_CMD_ST_ADDR                   = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR[dwpu_pkg::CMDB];
  //-//localparam DWPU_CMD_END_ADDR                  = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR[dwpu_pkg::CMDB];
  //-//localparam DWPU_IMEM_ST_ADDR                  = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR[dwpu_pkg::IMEM];
  //-//localparam DWPU_IMEM_END_ADDR                 = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR[dwpu_pkg::IMEM];
  //-//localparam DWPU_CSR_REGION_SIZE               = DWPU_CSR_END_ADDR - DWPU_CSR_ST_ADDR +1;
  //-//localparam DWPU_CMD_REGION_SIZE               = DWPU_CMD_END_ADDR - DWPU_CMD_ST_ADDR +1;
  //-//localparam DWPU_IMEM_REGION_SIZE              = INSTR_MEM_DEPTH * DWPU_INSTR_NUM_ROWS * 8;
  //-//localparam DWPU_CSR_REGION_END                = DWPU_CSR_END_ADDR;
  //-//localparam DWPU_CMD_REGION_END                = DWPU_CMD_END_ADDR;
  //-//localparam DWPU_IMEM_REGION_END               = DWPU_IMEM_ST_ADDR+DWPU_IMEM_REGION_SIZE-1;
  //-//localparam DWPU_CMD_MEM_WIDTH                 = $bits(aic_dp_cmd_gen_pkg::cmdb_cmd_t);
  //-//localparam DWPU_CMD_NUM_ROWS_FULL             = DWPU_CMD_MEM_WIDTH / AXI_LT_DATA_WIDTH; //without header
  //-//localparam DWPU_CMD_NUM_ROWS_BYPASS           = 0; //bypass command does not have payload
  //-//localparam DWPU_CMD_NUM_ROWS_M1N0            = 1;
  //-//localparam DWPU_CMD_NUM_ROWS_M1N1            = 2;
  //-//localparam DWPU_CMD_NUM_ROWS_M1N2            = 3;
  //-//localparam DWPU_CMD_NUM_ROWS_M2N0            = 2;
  //-//localparam DWPU_CMD_NUM_ROWS_M2N1            = 3;
  //-//localparam DWPU_CMD_NUM_ROWS_M2N2            = 4;
  //-//localparam DWPU_CMD_NUM_ROWS_M3N0            = 3;
  //-//localparam DWPU_CMD_NUM_ROWS_M3N1            = 4;
  //-//localparam DWPU_CMD_NUM_ROWS_M3N2            = 5;
  //-//localparam HEADER_CMD_TOK_PROD_WIDTH          = 16;
  //-//localparam HEADER_CMD_TOK_CONS_WIDTH          = 16;
  //-//localparam HEADER_CMD_RSVD_FORMAT_WIDTH       = 8-aic_dp_cmd_gen_pkg::CmdBlockFormatWidth;
  //-//localparam HEADER_CMD_RSVD_WIDTH              = 8;
  //-//localparam HEADER_CMD_TRIGGERS_WIDTH          = 8;
  //-//localparam HEADER_CMD_CONFIG_WIDTH            = 8;

  // ****************************************************************************
  // Typedefs used in whole testbench
  // ****************************************************************************

  //-//typedef dwpu_csr_reg_block DWPU_RAL;

  //-//typedef  bit [AXI_LT_ADDR_WIDTH-1:0] axi_lp_addr_t;
  //-//typedef  bit [AXI_LT_DATA_WIDTH-1:0] axi_lp_data_t;
  //-//typedef  bit [8 - 1:0] axi_lp_wstrb_t;

  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************
  
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m1n0_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_0;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m1n1_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_1;
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_0;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m1n2_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_1;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m2n0_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_0;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_1;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m2n1_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_1;
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_0;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_1;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m2n2_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_2;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_1;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m3n0_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_0;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_2;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_1;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m3n1_t;
  //-//
  //-//typedef struct packed {
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_1;
  //-//  aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t nested_0;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_2;
  //-//  aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_1;
  //-//  aic_dp_cmd_gen_pkg::command_extra_t    extra;
  //-//  aic_dp_cmd_gen_pkg::loop_description_t main_0;
  //-//} cmdb_cmd_m3n2_t;
  //-//
  //-//typedef struct {
  //-//  bit [31:0] main_dt_cnt[3];
  //-//  bit [31:0] nested_dt_cnt[2];
  //-//} data_stream_cfg_t;
  //-//
  //-//typedef struct packed {
  //-//  bit [HEADER_CMD_CONFIG_WIDTH-1:0]           h_config;
  //-//  bit [HEADER_CMD_RSVD_FORMAT_WIDTH-1:0]      rsvd_format;
  //-//  aic_dp_cmd_gen_pkg::cmd_format_e            format;
  //-//  bit [HEADER_CMD_TOK_CONS_WIDTH-1:0]         token_cons;
  //-//  bit [HEADER_CMD_TOK_PROD_WIDTH-1:0]         token_prod;
  //-//  bit [HEADER_CMD_RSVD_WIDTH-1:0]             rsvd;
  //-//  bit [HEADER_CMD_TRIGGERS_WIDTH-1:0]         triggers;
  //-//} dwpu_cmd_header_t;
  //-//
  //-//typedef enum bit [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] {
  //-//  DWPU_IRQ_ERR_ACT_STREAM_IN    = 'd0,
  //-//  DWPU_IRQ_ERR_ACT_STREAM_OUT   = 'd1,
  //-//  DWPU_IRQ_ERR_ILLEGAL_FORMAT   = 'd2,
  //-//  DWPU_IRQ_ERR_EMPTY_PROGRAM    = 'd3,
  //-//  DWPU_IRQ_ERR_INIT_LEN         = 'd4,
  //-//  DWPU_IRQ_ERR_OUTER_LEN        = 'd5,
  //-//  DWPU_IRQ_ERR_INNER0_LEN       = 'd6,
  //-//  DWPU_IRQ_ERR_INNER1_LEN       = 'd7,
  //-//  DWPU_IRQ_ERR_INNER0_SEGFAULT  = 'd8,
  //-//  DWPU_IRQ_ERR_INNER1_SEGFAULT  = 'd9,
  //-//  DWPU_IRQ_ERR_INNER1_NO_INNER0 = 'd10,
  //-//  DWPU_IRQ_ERR_INNER1_OVERLAP   = 'd11,
  //-//  DWPU_IRQ_CMDBLK_CMD_DROPPED   = 'd12,
  //-//  DWPU_IRQ_DBG_SW_INTERRUPT     = 'd32
  //-//} dwpu_irq_t;
  //-//
  //-//`include "ai_core_dwpu_cmd_tr.sv"
  //-//`include "ai_core_dwpu_utils.svh"
endpackage : ai_core_cd_common_pkg

