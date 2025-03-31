// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Address generation for the IFD_ODR
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_ADDR_GEN_SV_
`define _IFD_ODR_ADDR_GEN_SV_

`ifndef IFD_ODR_MAX
`define IFD_ODR_MAX(a, b) ((a)>(b)?(a):(b))
`endif

module ifd_odr_addr_gen
  import ifd_odr_pkg::*;
#(
  parameter type cmdgen_status_reg_t = logic
) (
  input wire i_clk,
  input wire i_rst_n,

  // output
  output logic                      dpc_vld,
  input  logic                      dpc_rdy,
  output logic [    IFD_ODR_DPC_ADDR_DW-1:0] dpc_addr,
  output logic [     IFD_ODR_DPC_MSK_DW-1:0] dpc_msk,
  output logic [  IFD_ODR_DPC_FORMAT_DW-1:0] dpc_format,
  output logic                               dpc_config,
  output logic                      dpc_pad,
  output logic                      dpc_last,
  output logic [ IFD_ODR_DPC_PAD_VAL_DW-1:0] dpc_pad_val,
  output logic [ IFD_ODR_DPC_INTRA_PAD_VAL_DW-1:0] dpc_intra_pad_val,

  output logic err_addr_out_of_range,

  // addr gen command:
  input  logic [IFD_ODR_AG_CMD_DW-1:0] ag_cmd,
  input  logic                         ag_config,
  input  logic                 ag_vld,
  output logic                 ag_rdy,

  // State observation
  output cmdgen_status_reg_t cmdgen_status

);

  // pword granularity for addresses
  localparam int unsigned AddrGrW = $clog2(IFD_ODR_PWORD64_LEN);
  localparam int unsigned IfdOdrAgDimWDw =
    `IFD_ODR_MAX(IFD_ODR_AG_DIM_W_A_DW,
      `IFD_ODR_MAX(IFD_ODR_AG_DIM_W_B_DW,
        `IFD_ODR_MAX(IFD_ODR_AG_DIM_W_C_DW, IFD_ODR_AG_DIM_W_D_DW)));

  logic                                              pad_del_d;
  reg          [IFD_ODR_LAT_COORD__2_OUT:0]                   pad_del;
  logic                                              vect_pad_del_d;
  reg          [IFD_ODR_LAT_COORD__2_OUT:0]                   vect_pad_del;
  logic                           [IFD_ODR_INT_COORD_DW-1:0] coord_del_d;
  reg          [IFD_ODR_LAT_COORD__2_OUT:0][IFD_ODR_INT_COORD_DW-1:0] coord_del;
  logic                                              err_addr_out_of_range_calc;

  // config registers
  reg          [             IFD_ODR_AG_CMD_DW-1:0] ag_cmd_q;
  logic                                             ag_config_q;

  logic        [     IFD_ODR_AG_INNER_LEN_A_DW-1:0] inner_len_a;
  logic        [     IFD_ODR_AG_INNER_LEN_B_DW-1:0] inner_len_b;
  logic        [     IFD_ODR_AG_INNER_LEN_C_DW-1:0] inner_len_c;
  logic        [     IFD_ODR_AG_INNER_LEN_D_DW-1:0] inner_len_d;
  logic signed [     IFD_ODR_AG_INNER_STR_A_DW-1:0] inner_str_a;
  logic signed [     IFD_ODR_AG_INNER_STR_B_DW-1:0] inner_str_b;
  logic signed [     IFD_ODR_AG_INNER_STR_C_DW-1:0] inner_str_c;
  logic signed [     IFD_ODR_AG_INNER_STR_D_DW-1:0] inner_str_d;
  logic        [     IFD_ODR_AG_OUTER_LEN_A_DW-1:0] outer_len_a;
  logic        [     IFD_ODR_AG_OUTER_LEN_B_DW-1:0] outer_len_b;
  logic        [     IFD_ODR_AG_OUTER_LEN_C_DW-1:0] outer_len_c;
  logic        [     IFD_ODR_AG_OUTER_LEN_D_DW-1:0] outer_len_d;
  logic signed [     IFD_ODR_AG_OUTER_STR_A_DW-1:0] outer_str_a;
  logic signed [     IFD_ODR_AG_OUTER_STR_B_DW-1:0] outer_str_b;
  logic signed [     IFD_ODR_AG_OUTER_STR_C_DW-1:0] outer_str_c;
  logic signed [     IFD_ODR_AG_OUTER_STR_D_DW-1:0] outer_str_d;

  logic        [         IFD_ODR_AG_DIM_W_A_DW-1:0] dim_w_a;
  logic        [         IFD_ODR_AG_DIM_W_B_DW-1:0] dim_w_b;
  logic        [         IFD_ODR_AG_DIM_W_C_DW-1:0] dim_w_c;
  logic        [         IFD_ODR_AG_DIM_W_D_DW-1:0] dim_w_d;
  logic signed [       IFD_ODR_AG_DIM_OFF_A_DW-1:0] dim_off_a;
  logic signed [       IFD_ODR_AG_DIM_OFF_B_DW-1:0] dim_off_b;
  logic signed [       IFD_ODR_AG_DIM_OFF_C_DW-1:0] dim_off_c;
  logic signed [       IFD_ODR_AG_DIM_OFF_D_DW-1:0] dim_off_d;

  logic        [       IFD_ODR_AG_MSK_START_DW-1:0] msk_start;
  logic        [         IFD_ODR_AG_MSK_END_DW-1:0] msk_end;

  logic        [        IFD_ODR_AG_MEM_BASE_DW-1:0] mem_base_pre_g;
  logic        [       IFD_ODR_AG_MEM_BSIZE_DW-1:0] mem_bsize_pre_g;
  logic        [    IFD_ODR_AG_MEM_STRIDE_A_DW-1:0] mem_stride_a_pre_g;
  logic        [    IFD_ODR_AG_MEM_STRIDE_B_DW-1:0] mem_stride_b_pre_g;
  logic        [    IFD_ODR_AG_MEM_STRIDE_C_DW-1:0] mem_stride_c_pre_g;
  logic        [    IFD_ODR_AG_MEM_STRIDE_D_DW-1:0] mem_stride_d_pre_g;
  logic        [      IFD_ODR_AG_MEM_OFFSET_DW-1:0] mem_offset_pre_g;
  logic        [        IFD_ODR_AG_MEM_BASE_DW-1:0] mem_base;
  logic        [       IFD_ODR_AG_MEM_BSIZE_DW-1:0] mem_bsize;
  logic        [    IFD_ODR_AG_MEM_STRIDE_A_DW-1:0] mem_stride_a;
  logic        [    IFD_ODR_AG_MEM_STRIDE_B_DW-1:0] mem_stride_b;
  logic        [    IFD_ODR_AG_MEM_STRIDE_C_DW-1:0] mem_stride_c;
  logic        [    IFD_ODR_AG_MEM_STRIDE_D_DW-1:0] mem_stride_d;
  logic        [      IFD_ODR_AG_MEM_OFFSET_DW-1:0] mem_offset;

  logic        [IFD_ODR_AG_RING_BUFFER_SIZE_DW-1:0] ring_buff_size;

  logic        [         IFD_ODR_AG_PAD_VAL_DW-1:0] pad_val;
  logic        [   IFD_ODR_AG_INTRA_PAD_VAL_DW-1:0] intra_pad_val;
  logic        [   IFD_ODR_AG_PAD_MODE_EDGE_DW-1:0] pad_mode;
  logic        [        IFD_ODR_AG_VECT_DIM_DW-1:0] vect_dim;

  // // control
  logic                                     loop_busy;
  logic                                     start;
  logic                                     pipe_en;
  logic outer_a_incr, outer_a_set0;
  logic outer_b_incr, outer_b_set0;
  logic outer_c_incr, outer_c_set0;
  logic outer_d_incr, outer_d_set0;
  logic inner_a_incr, inner_a_set0;
  logic inner_b_incr, inner_b_set0;
  logic inner_c_incr, inner_c_set0;
  logic inner_d_incr, inner_d_set0;
  logic vect_en_a, vect_en_b, vect_en_c, vect_en_d;

  // intermediate calculation results
  logic [ IFD_ODR_INT_ADDR_DW-1:0] addr_a;
  logic [ IFD_ODR_INT_ADDR_DW-1:0] addr_b;
  logic [ IFD_ODR_INT_ADDR_DW-1:0] addr_c;
  logic [ IFD_ODR_INT_ADDR_DW-1:0] addr_d;
  logic                    pad_a;
  logic                    pad_b;
  logic                    pad_c;
  logic                    pad_d;
  logic [IFD_ODR_INT_COORD_DW-1:0] coord_a;
  logic [IFD_ODR_INT_COORD_DW-1:0] coord_b;
  logic [IFD_ODR_INT_COORD_DW-1:0] coord_c;
  logic [IFD_ODR_INT_COORD_DW-1:0] coord_d;

  // vectorized selection:
  logic [ IfdOdrAgDimWDw-1:0] dim_w_vect;
  logic [IFD_ODR_INT_COORD_DW-1:0] coord_vect;

  assign dpc_pad_val = pad_val;
  assign dpc_intra_pad_val = intra_pad_val;

  // catch config regs, does not need a reset:
  // spyglass disable_block STARC05-3.3.1.4b
  // spyglass disable_block STARC-2.3.4.3
  always_ff @(posedge i_clk) begin : cfg_regs
    if (start == 1'b1) begin
      ag_cmd_q    <= ag_cmd;
      ag_config_q <= ag_config;
    end
  end
  // spyglass enable_block STARC-2.3.4.3
  // spyglass enable_block STARC05-3.3.1.4b
  assign ag_rdy = ~loop_busy;
  assign start = ag_vld & ~loop_busy;

  // assign cfg reg to cfg lines:
  assign dim_w_a = ag_cmd_q[IFD_ODR_AG_DIM_W_A_LSB+:IFD_ODR_AG_DIM_W_A_DW];
  assign dim_w_b = ag_cmd_q[IFD_ODR_AG_DIM_W_B_LSB+:IFD_ODR_AG_DIM_W_B_DW];
  assign dim_w_c = ag_cmd_q[IFD_ODR_AG_DIM_W_C_LSB+:IFD_ODR_AG_DIM_W_C_DW];
  assign dim_w_d = ag_cmd_q[IFD_ODR_AG_DIM_W_D_LSB+:IFD_ODR_AG_DIM_W_D_DW];
  assign dim_off_a = signed'(ag_cmd_q[IFD_ODR_AG_DIM_OFF_A_LSB+:IFD_ODR_AG_DIM_OFF_A_DW]);
  assign dim_off_b = signed'(ag_cmd_q[IFD_ODR_AG_DIM_OFF_B_LSB+:IFD_ODR_AG_DIM_OFF_B_DW]);
  assign dim_off_c = signed'(ag_cmd_q[IFD_ODR_AG_DIM_OFF_C_LSB+:IFD_ODR_AG_DIM_OFF_C_DW]);
  assign dim_off_d = signed'(ag_cmd_q[IFD_ODR_AG_DIM_OFF_D_LSB+:IFD_ODR_AG_DIM_OFF_D_DW]);
  assign inner_len_a = ag_cmd_q[IFD_ODR_AG_INNER_LEN_A_LSB+:IFD_ODR_AG_INNER_LEN_A_DW];
  assign inner_len_b = ag_cmd_q[IFD_ODR_AG_INNER_LEN_B_LSB+:IFD_ODR_AG_INNER_LEN_B_DW];
  assign inner_len_c = ag_cmd_q[IFD_ODR_AG_INNER_LEN_C_LSB+:IFD_ODR_AG_INNER_LEN_C_DW];
  assign inner_len_d = ag_cmd_q[IFD_ODR_AG_INNER_LEN_D_LSB+:IFD_ODR_AG_INNER_LEN_D_DW];
  assign inner_str_a = signed'(ag_cmd_q[IFD_ODR_AG_INNER_STR_A_LSB+:IFD_ODR_AG_INNER_STR_A_DW]);
  assign inner_str_b = signed'(ag_cmd_q[IFD_ODR_AG_INNER_STR_B_LSB+:IFD_ODR_AG_INNER_STR_B_DW]);
  assign inner_str_c = signed'(ag_cmd_q[IFD_ODR_AG_INNER_STR_C_LSB+:IFD_ODR_AG_INNER_STR_C_DW]);
  assign inner_str_d = signed'(ag_cmd_q[IFD_ODR_AG_INNER_STR_D_LSB+:IFD_ODR_AG_INNER_STR_D_DW]);
  assign outer_len_a = ag_cmd_q[IFD_ODR_AG_OUTER_LEN_A_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW];
  assign outer_len_b = ag_cmd_q[IFD_ODR_AG_OUTER_LEN_B_LSB+:IFD_ODR_AG_OUTER_LEN_B_DW];
  assign outer_len_c = ag_cmd_q[IFD_ODR_AG_OUTER_LEN_C_LSB+:IFD_ODR_AG_OUTER_LEN_C_DW];
  assign outer_len_d = ag_cmd_q[IFD_ODR_AG_OUTER_LEN_D_LSB+:IFD_ODR_AG_OUTER_LEN_D_DW];
  assign outer_str_a = signed'(ag_cmd_q[IFD_ODR_AG_OUTER_STR_A_LSB+:IFD_ODR_AG_OUTER_STR_A_DW]);
  assign outer_str_b = signed'(ag_cmd_q[IFD_ODR_AG_OUTER_STR_B_LSB+:IFD_ODR_AG_OUTER_STR_B_DW]);
  assign outer_str_c = signed'(ag_cmd_q[IFD_ODR_AG_OUTER_STR_C_LSB+:IFD_ODR_AG_OUTER_STR_C_DW]);
  assign outer_str_d = signed'(ag_cmd_q[IFD_ODR_AG_OUTER_STR_D_LSB+:IFD_ODR_AG_OUTER_STR_D_DW]);

  assign msk_start = dpc_format ? ag_cmd_q[IFD_ODR_AG_MSK_START_LSB+:IFD_ODR_AG_MSK_START_DW] << 1 :
                                                  ag_cmd_q[IFD_ODR_AG_MSK_START_LSB+:IFD_ODR_AG_MSK_START_DW];
  assign msk_end = dpc_format ? ag_cmd_q[IFD_ODR_AG_MSK_END_LSB+:IFD_ODR_AG_MSK_END_DW] << 1 :
                                                ag_cmd_q[IFD_ODR_AG_MSK_END_LSB+:IFD_ODR_AG_MSK_END_DW];

  assign mem_base_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_BASE_LSB+:IFD_ODR_AG_MEM_BASE_DW];
  assign mem_bsize_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_BSIZE_LSB+:IFD_ODR_AG_MEM_BSIZE_DW];
  assign mem_stride_a_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_STRIDE_A_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW];
  assign mem_stride_b_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_STRIDE_B_LSB+:IFD_ODR_AG_MEM_STRIDE_B_DW];
  assign mem_stride_c_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_STRIDE_C_LSB+:IFD_ODR_AG_MEM_STRIDE_C_DW];
  assign mem_stride_d_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_STRIDE_D_LSB+:IFD_ODR_AG_MEM_STRIDE_D_DW];
  assign mem_offset_pre_g = ag_cmd_q[IFD_ODR_AG_MEM_OFFSET_LSB+:IFD_ODR_AG_MEM_OFFSET_DW];

  assign mem_base = {mem_base_pre_g[$bits(mem_base_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}};
  assign mem_bsize = {mem_bsize_pre_g[$bits(mem_bsize_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}};
  assign mem_stride_a = {
    mem_stride_a_pre_g[$bits(mem_stride_a_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}
  };
  assign mem_stride_b = {
    mem_stride_b_pre_g[$bits(mem_stride_b_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}
  };
  assign mem_stride_c = {
    mem_stride_c_pre_g[$bits(mem_stride_c_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}
  };
  assign mem_stride_d = {
    mem_stride_d_pre_g[$bits(mem_stride_d_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}
  };
  assign mem_offset = {mem_offset_pre_g[$bits(mem_offset_pre_g)-1:AddrGrW], {AddrGrW{1'b0}}};

  assign ring_buff_size = ag_cmd_q[IFD_ODR_AG_RING_BUFFER_SIZE_DW +
                                     IFD_ODR_AG_RING_BUFFER_SIZE_LSB-1 :
                                       IFD_ODR_AG_RING_BUFFER_SIZE_LSB];
  assign pad_val = ag_cmd_q[IFD_ODR_AG_PAD_VAL_LSB+:IFD_ODR_AG_PAD_VAL_DW];
  assign intra_pad_val = ag_cmd_q[IFD_ODR_AG_INTRA_PAD_VAL_LSB+:IFD_ODR_AG_INTRA_PAD_VAL_DW];
  assign pad_mode = ag_cmd_q[IFD_ODR_AG_PAD_MODE_EDGE_LSB+:IFD_ODR_AG_PAD_MODE_EDGE_DW];
  assign vect_dim = ag_cmd_q[IFD_ODR_AG_VECT_DIM_LSB+:IFD_ODR_AG_VECT_DIM_DW];

  assign dpc_format = ag_cmd_q[IFD_ODR_AG_FORMAT_LSB+:IFD_ODR_AG_FORMAT_DW];
  assign dpc_config = ag_config_q;

  always_comb begin : vect_sel
    unique case (vect_dim)
      0: begin
        dim_w_vect = dim_w_a;
        coord_vect = coord_a;
      end
      1: begin
        dim_w_vect = dim_w_b;
        coord_vect = coord_b;
      end
      2: begin
        dim_w_vect = dim_w_c;
        coord_vect = coord_c;
      end
      3: begin
        dim_w_vect = dim_w_d;
        coord_vect = coord_d;
      end
      default: begin
        dim_w_vect = dim_w_a;
        coord_vect = coord_a;
      end
    endcase
  end
  assign vect_en_a = (vect_dim == 0) ? 1'b1 : 1'b0;
  assign vect_en_b = (vect_dim == 1) ? 1'b1 : 1'b0;
  assign vect_en_c = (vect_dim == 2) ? 1'b1 : 1'b0;
  assign vect_en_d = (vect_dim == 3) ? 1'b1 : 1'b0;

  // control part:
  ifd_odr_loop_ctrl #(
    .cmdgen_status_reg_t(cmdgen_status_reg_t)
  ) u_loop_ctrl (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start),
    .busy(loop_busy),
    .pipe_en(pipe_en),
    .last(dpc_last),

    .outer_len_a(outer_len_a),
    .outer_len_b(outer_len_b),
    .outer_len_c(outer_len_c),
    .outer_len_d(outer_len_d),
    .inner_len_a(inner_len_a),
    .inner_len_b(inner_len_b),
    .inner_len_c(inner_len_c),
    .inner_len_d(inner_len_d),

    .outer_a_incr(outer_a_incr),
    .outer_a_set0(outer_a_set0),
    .outer_b_incr(outer_b_incr),
    .outer_b_set0(outer_b_set0),
    .outer_c_incr(outer_c_incr),
    .outer_c_set0(outer_c_set0),
    .outer_d_incr(outer_d_incr),
    .outer_d_set0(outer_d_set0),
    .inner_a_incr(inner_a_incr),
    .inner_a_set0(inner_a_set0),
    .inner_b_incr(inner_b_incr),
    .inner_b_set0(inner_b_set0),
    .inner_c_incr(inner_c_incr),
    .inner_c_set0(inner_c_set0),
    .inner_d_incr(inner_d_incr),
    .inner_d_set0(inner_d_set0),

    .addr_vld(dpc_vld),
    .addr_rdy(dpc_rdy),

    .cmdgen_status
  );

  // coordination calculation for coord_a
  ifd_odr_dim_addr #(
    .INNER_STR_W(IFD_ODR_AG_INNER_STR_A_DW),
    .INNER_LEN_W(IFD_ODR_AG_INNER_LEN_A_DW),
    .OUTER_STR_W(IFD_ODR_AG_OUTER_STR_A_DW),
    .OUTER_LEN_W(IFD_ODR_AG_OUTER_LEN_A_DW),
    .DIM_OFF_W(IFD_ODR_AG_DIM_OFF_A_DW),
    .DIM_W_W(IFD_ODR_AG_DIM_W_A_DW),
    .COORD_W(IFD_ODR_INT_COORD_DW),
    .MEM_STRD_W(IFD_ODR_AG_MEM_STRIDE_A_DW),
    .ADDR_W(IFD_ODR_INT_ADDR_DW)
  ) u_dim_addr_a (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .inner_incr(inner_a_incr),
    .inner_set0(inner_a_set0),
    .inner_strd(inner_str_a),

    .outer_incr(outer_a_incr),
    .outer_set0(outer_a_set0),
    .outer_strd(outer_str_a),

    .offset(dim_off_a),
    .dim_w (dim_w_a),

    .pad_mode(pad_mode),
    .pipe_en (pipe_en),

    .mem_strd(mem_stride_a),

    .coord_out(coord_a),
    .vect_en(vect_en_a),
    .addr_out(addr_a),
    .pad(pad_a)
  );

  // coordination calculation for coord_b
  ifd_odr_dim_addr #(
    .INNER_STR_W(IFD_ODR_AG_INNER_STR_B_DW),
    .INNER_LEN_W(IFD_ODR_AG_INNER_LEN_B_DW),
    .OUTER_STR_W(IFD_ODR_AG_OUTER_STR_B_DW),
    .OUTER_LEN_W(IFD_ODR_AG_OUTER_LEN_B_DW),
    .DIM_OFF_W(IFD_ODR_AG_DIM_OFF_B_DW),
    .DIM_W_W(IFD_ODR_AG_DIM_W_B_DW),
    .COORD_W(IFD_ODR_INT_COORD_DW),
    .MEM_STRD_W(IFD_ODR_AG_MEM_STRIDE_B_DW),
    .ADDR_W(IFD_ODR_INT_ADDR_DW)
  ) u_dim_addr_b (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .inner_incr(inner_b_incr),
    .inner_set0(inner_b_set0),
    .inner_strd(inner_str_b),

    .outer_incr(outer_b_incr),
    .outer_set0(outer_b_set0),
    .outer_strd(outer_str_b),

    .offset(dim_off_b),
    .dim_w (dim_w_b),

    .pad_mode(pad_mode),
    .pipe_en (pipe_en),

    .mem_strd(mem_stride_b),

    .coord_out(coord_b),
    .vect_en(vect_en_b),
    .addr_out(addr_b),
    .pad(pad_b)
  );

  // coordination calculation for coord_c:
  ifd_odr_dim_addr #(
    .INNER_STR_W(IFD_ODR_AG_INNER_STR_C_DW),
    .INNER_LEN_W(IFD_ODR_AG_INNER_LEN_C_DW),
    .OUTER_STR_W(IFD_ODR_AG_OUTER_STR_C_DW),
    .OUTER_LEN_W(IFD_ODR_AG_OUTER_LEN_C_DW),
    .DIM_OFF_W(IFD_ODR_AG_DIM_OFF_C_DW),
    .DIM_W_W(IFD_ODR_AG_DIM_W_C_DW),
    .COORD_W(IFD_ODR_INT_COORD_DW),
    .MEM_STRD_W(IFD_ODR_AG_MEM_STRIDE_C_DW),
    .ADDR_W(IFD_ODR_INT_ADDR_DW)
  ) u_dim_addr_c (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .inner_incr(inner_c_incr),
    .inner_set0(inner_c_set0),
    .inner_strd(inner_str_c),

    .outer_incr(outer_c_incr),
    .outer_set0(outer_c_set0),
    .outer_strd(outer_str_c),

    .offset(dim_off_c),
    .dim_w (dim_w_c),

    .pad_mode(pad_mode),
    .pipe_en (pipe_en),

    .mem_strd(mem_stride_c),

    .coord_out(coord_c),
    .vect_en(vect_en_c),
    .addr_out(addr_c),
    .pad(pad_c)
  );

  // coordination calculation for coord_d:
  ifd_odr_dim_addr #(
    .INNER_STR_W(IFD_ODR_AG_INNER_STR_D_DW),
    .INNER_LEN_W(IFD_ODR_AG_INNER_LEN_D_DW),
    .OUTER_STR_W(IFD_ODR_AG_OUTER_STR_D_DW),
    .OUTER_LEN_W(IFD_ODR_AG_OUTER_LEN_D_DW),
    .DIM_OFF_W(IFD_ODR_AG_DIM_OFF_D_DW),
    .DIM_W_W(IFD_ODR_AG_DIM_W_D_DW),
    .COORD_W(IFD_ODR_INT_COORD_DW),
    .MEM_STRD_W(IFD_ODR_AG_MEM_STRIDE_D_DW),
    .ADDR_W(IFD_ODR_INT_ADDR_DW)
  ) u_dim_addr_d (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .inner_incr(inner_d_incr),
    .inner_set0(inner_d_set0),
    .inner_strd(inner_str_d),

    .outer_incr(outer_d_incr),
    .outer_set0(outer_d_set0),
    .outer_strd(outer_str_d),

    .offset(dim_off_d),
    .dim_w (dim_w_d),

    .pad_mode(pad_mode),
    .pipe_en (pipe_en),

    .mem_strd(mem_stride_d),

    .coord_out(coord_d),
    .vect_en(vect_en_d),
    .addr_out(addr_d),
    .pad(pad_d)
  );

  // calculate the address
  ifd_odr_addr_calc #(
    .MEM_COORD_ADDR_W(IFD_ODR_INT_ADDR_DW),
    .ABS_BUFF_W(IFD_ODR_AG_MEM_BASE_DW)
  ) u_addr_calc (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .pipe_en(pipe_en),

    .addr_a(addr_a),
    .addr_b(addr_b),
    .addr_c(addr_c),
    .addr_d(addr_d),

    .mem_offset(mem_offset),
    .mem_base(mem_base),
    .mem_bsize(mem_bsize),
    .ring_buff_size(ring_buff_size),

    .addr(dpc_addr),
    .err_addr_out_of_range(err_addr_out_of_range_calc)
  );

  // padding check:
  always_comb pad_del_d = pad_a | pad_b | pad_c | pad_d;
  always_comb vect_pad_del_d = (pad_a & vect_en_a) |
                               (pad_b & vect_en_b) |
                               (pad_c & vect_en_c) |
                               (pad_d & vect_en_d);
  assign dpc_pad = pad_del[IFD_ODR_LAT_COORD__2_OUT];

  // no error out of range when padding:
  assign err_addr_out_of_range = err_addr_out_of_range_calc & ~pad_del[IFD_ODR_LAT_COORD__2_OUT];

  ifd_odr_inner_pad #(
    .COORD_W(IFD_ODR_INT_COORD_DW),
    .DIM_W_W(IfdOdrAgDimWDw)
  ) u_inner_pad_check (
    .coord(coord_del[IFD_ODR_LAT_COORD__2_OUT]),
    .dim_w(dim_w_vect),
    .vect_pad(vect_pad_del[IFD_ODR_LAT_COORD__2_OUT]),
    .msk_start(msk_start),
    .msk_end(msk_end),
    .inner_pad(dpc_msk)
  );

  // delay path, no need for reset:
  always_comb coord_del_d = coord_vect;

  always_ff @(negedge i_rst_n or posedge i_clk) begin
    if (i_rst_n == 1'b0) begin
      pad_del <= '0;
      vect_pad_del <= '0;
      coord_del <= '0;
    end else if (pipe_en) begin
      for (int i = 0; i < IFD_ODR_LAT_COORD__2_OUT; i++) begin
        pad_del[i+1] <= (i==0) ? pad_del_d : pad_del[i];
        vect_pad_del[i+1] <= (i==0) ? vect_pad_del_d : vect_pad_del[i];
        coord_del[i+1] <= (i==0) ? coord_del_d : coord_del[i];
      end
    end
  end

endmodule

`endif  // _IFD_ODR_ADDR_GEN_SV_
