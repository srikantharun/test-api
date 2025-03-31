`ifndef DMC_ADDR_GEN_IF
`define DMC_ADDR_GEN_IF

/*******************************************************************************************
********************************************************************************************
any additions in if file - don't forget to connect in rtl folder under the appropriate file!
********************************************************************************************
*******************************************************************************************/

interface dmc_addr_gen_if (input clk);

  typedef struct packed {
    // word 9
    logic[ 7:0] outer_stride_d;  // parameter AG_OUTER_STR_D_LSB = 624;
    logic[15:0] outer_length_d;  // parameter AG_OUTER_LEN_D_LSB = 608;
    logic[ 7:0] dummy_byte_w9;   // dummy byte in w9
    logic[ 7:0] inner_stride_d;  // parameter AG_INNER_STR_D_LSB = 592;
    logic[15:0] inner_length_d;  // parameter AG_INNER_LEN_D_LSB = 576;
    // word 8
    logic[31:0] mem_stride_d;    // parameter AG_MEM_STRIDE_D_LSB = 544;
    logic[15:0] dim_width_d;     // parameter AG_DIM_W_D_LSB = 528;
    logic[15:0] dim_offset_d;    // parameter AG_DIM_OFF_D_LSB = 512;
    //word 7
    logic[ 7:0] outer_stride_c;  // parameter AG_OUTER_STR_C_LSB = 504;
    logic[ 7:0] inner_stride_c;  // parameter AG_INNER_STR_C_LSB = 496;
    logic[ 7:0] outer_stride_b;  // parameter AG_OUTER_STR_B_LSB = 488;
    logic[ 7:0] inner_stride_b;  // parameter AG_INNER_STR_B_LSB = 480;
    logic[15:0] outer_length_b;  // parameter AG_OUTER_LEN_B_LSB = 464;
    logic[15:0] inner_length_b;  // parameter AG_INNER_LEN_B_LSB = 448;
    //word 6
    logic[15:0] outer_length_c;  // parameter AG_OUTER_LEN_C_LSB = 432;
    logic[ 7:0] outer_stride_a;  // parameter AG_OUTER_STR_A_LSB = 424;
    logic[ 7:0] inner_stride_a;  // parameter AG_INNER_STR_A_LSB = 416;
    logic[15:0] outer_length_a;  // parameter AG_OUTER_LEN_A_LSB = 400;
    logic[15:0] inner_length_a;  // parameter AG_INNER_LEN_A_LSB = 384;
    //word 5
    logic[31:0] mem_stride_c;    // parameter AG_MEM_STRIDE_C_LSB = 352;
    logic[15:0] dim_width_c;     // parameter AG_DIM_W_C_LSB = 336;
    logic[15:0] dim_offset_c;    // parameter AG_DIM_OFF_C_LSB = 320;
    //word 4
    logic[31:0] mem_stride_b;    // parameter AG_MEM_STRIDE_B_LSB = 288;
    logic[15:0] dim_width_b;     // parameter AG_DIM_W_B_LSB = 272;
    logic[15:0] dim_offset_b;    // parameter AG_DIM_OFF_B_LSB = 256;
    //word 3
    logic[31:0] mem_stride_a;    // parameter AG_MEM_STRIDE_A_LSB = 224;
    logic[15:0] dim_width_a;     // parameter AG_DIM_W_A_LSB = 208;
    logic[15:0] dim_offset_a;    // parameter AG_DIM_OFF_A_LSB = 192;
    //word 2
    logic[31:0] mem_bsize;        // parameter AG_MEM_BSIZE_LSB = 160;
    logic       decomp_en;        // parameter AG_DECOMP_EN_LSB = 152 + 7;  // for now just placing it in some empty spot
    logic[ 1:0] pad_dummy_w2_msb; // settings bit 6:5
    logic       pad_mode;        // parameter AG_PAD_MODE_EDGE_LSB = 152 + 4;  // settings bit 4
    logic       format;        // parameter AG_PAD_MODE_EDGE_LSB = 152 + 4;  // settings bit 4
    logic[ 1:0] vtrsp_mode;      // parameter AG_VTRSP_EN_LSB = 152 + 2;  // settings bit 2
    logic[ 1:0] vect_dim;        // parameter AG_VECT_DIM_LSB = 152 + 0;  // settings bit 1:0
    logic[ 7:0] dummy_byte_w3;   // dummy byte in w3
    logic[15:0] inner_length_c;  // parameter AG_INNER_LEN_C_LSB = 128;
    //word 1
    logic[23:0] ring_buff_size; // parameter AG_RING_BUFFER_SIZE_LSB = 96;
    logic[31:0] mem_offset;     // parameter AG_MEM_OFFSET_LSB = 64;
    //word 0
    logic[ 7:0] mask_end;       // parameter AG_MSK_END_LSB = 56;
    logic[ 7:0] mask_start;     // parameter AG_MSK_START_LSB = 48;
    logic[15:0] pad_val;        // parameter AG_PAD_VAL_LSB = 40;
    logic[15:0] intra_pad_val;
    logic[31:0] mem_baseaddr;   // parameter AG_MEM_BASE_LSB = 0;
  } addr_gen_cmd_interface_t;

  logic       reset_an_i;
  logic       dpc_vld;
  logic       dpc_rdy;
  logic[31:0] dpc_addr;
  logic[63:0] dpc_msk;
  logic       dpc_format;
  logic       dpc_config;
  logic       dpc_pad;
  logic       dpc_last;
  logic[15:0] dpc_pad_val;
  logic[15:0] dpc_intra_pad_val;
  logic       err_addr_out_of_range;

  addr_gen_cmd_interface_t ag_cmd;
  logic                    ag_vld;
  logic                    ag_rdy;

  clocking mon @(posedge clk);
    input reset_an_i;
    input dpc_vld;
    input dpc_rdy;
    input dpc_addr;
    input dpc_msk;
    input dpc_format;
    input dpc_config;
    input dpc_pad;
    input dpc_last;
    input dpc_pad_val;
    input dpc_intra_pad_val;
    input err_addr_out_of_range;
    input ag_cmd;
    input ag_vld;
    input ag_rdy;
  endclocking

  clocking drv @(posedge clk);
    output ag_cmd;
    output ag_vld;
    input  ag_rdy;
    output dpc_rdy;
  endclocking

endinterface

`endif

