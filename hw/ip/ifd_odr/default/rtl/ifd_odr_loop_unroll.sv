// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Loop unroll control and command forming for IFD and ODR
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_LOOP_UNROLL_SV_
`define _IFD_LOOP_UNROLL_SV_

module ifd_odr_loop_unroll #(
  parameter int unsigned DEFMEM_ROW_DW = 2
) (
  input wire i_clk,
  input wire i_rst_n,

  // CMDB connection:
  input logic cmdb_vld,
  input logic [ifd_odr_pkg::IFD_ODR_CMDB_MAX_CMD_DW-1:0] cmdb_cmd,
  input logic [$clog2(ifd_odr_pkg::CMD_NR_FORMATS)-1:0] cmdb_format,
  input logic cmdb_config,
  output logic cmdb_rdy,

  // AG cmdb connection:
  output logic ag_vld,
  output logic [ifd_odr_pkg::IFD_ODR_UNROLL_CMD_DW-1:0] ag_cmd,
  output logic [$clog2(ifd_odr_pkg::CMD_NR_FORMATS)-1:0] ag_format,
  output logic ag_config,
  input logic ag_rdy,

  // memory connection
  output logic [DEFMEM_ROW_DW-1:0] defmem_raddr,
  output logic                     defmem_rvld,
  input  logic                     defmem_rrdy,

  // resp:
  input logic [ifd_odr_pkg::IFD_ODR_DEFMEM_WIDTH-1:0] defmem_resp_data,
  input logic                                         defmem_resp_vld
);

  import ifd_odr_pkg::*;

  typedef enum logic [1:0] {
    IDLE,
    LOOP_FORM,
    LOOP_FINISH
  } fsm_t;

  reg [IFD_ODR_CMDB_MAX_CMD_DW+$clog2(CMD_NR_FORMATS)-1:0] cmdb_cmd_q;
  logic cmdb_config_q;
  logic [IFD_ODR_CMDB_MAX_CMD_DW-1:0] ag_cmd_pre_ext;
  reg cmdb_cmd_vld_q;
  logic cmdb_cmd_en, cmdb_cmd_vld_en;
  logic cmdb_cmd_vld_set, cmdb_cmd_vld_clr;
  logic cmdb_format_lm;

  fsm_t state_q, state_d;
  logic state_en;

  logic
      req_dim_loop_n,
      resp_dim_loop_n;  // counter uses one bit extra to select between dim or loop def

  localparam int unsigned NUMDIM_PLUS_1_DW = $clog2(IFD_ODR_DEFMEM_MAX_LOOPS+1);
  logic [NUMDIM_PLUS_1_DW:0] cmd_numdim_p1;

  reg [NUMDIM_PLUS_1_DW+1:0] req_cnt_q, resp_cnt_q;
  logic [NUMDIM_PLUS_1_DW+1:0] req_cnt_d, resp_cnt_d;
  logic req_cnt_en, req_cnt_start, req_cnt_incr;
  logic resp_cnt_en, resp_cnt_start, resp_cnt_incr;

  reg [IFD_ODR_DEFMEM_MAX_LOOPS-1:0][IFD_ODR_DEFMEM_WIDTH-1:0] dim_def_q, loop_def_q;
  logic [IFD_ODR_DEFMEM_MAX_LOOPS-1:0][IFD_ODR_DEFMEM_WIDTH-1:0] dim_def_d, loop_def_d;
  logic [IFD_ODR_DEFMEM_MAX_LOOPS-1:0] dim_def_en, loop_def_en;

  assign req_dim_loop_n = ~req_cnt_q[0];
  assign resp_dim_loop_n = ~resp_cnt_q[0];

  assign req_cnt_en = req_cnt_start | req_cnt_incr;
  assign resp_cnt_en = resp_cnt_start | resp_cnt_incr;

  assign req_cnt_d = (req_cnt_start) ? '0 : req_cnt_q + 1;
  assign resp_cnt_d = (resp_cnt_start) ? '0 : resp_cnt_q + 1;

  always_comb cmd_numdim_p1 = cmdb_cmd_q[IFD_ODR_DEFMEM_NUMDIM_LSB+:IFD_ODR_DEFMEM_NUMDIM_DW]+1; // 1 dim is encoded as 0 in num_dim

  // address request is current loop count plus the asked ptr:
  // truncation can happen and is allowed:
  // spyglass disable_block W164a_a
  assign defmem_raddr = req_cnt_q[NUMDIM_PLUS_1_DW:1] + (req_dim_loop_n ?
                          cmdb_cmd_q[IFD_ODR_DEFMEM_DIM_DEF_PTR_LSB+:IFD_ODR_DEFMEM_DIM_DEF_PTR_DW] :
                          cmdb_cmd_q[IFD_ODR_DEFMEM_LOOP_DEF_PTR_LSB+:IFD_ODR_DEFMEM_LOOP_DEF_PTR_DW]);
  // spyglass enable_block W164a_a

  assign cmdb_format_lm = ((cmdb_format == IFD_ODR_CMD_DM_BASE_FMT) || (cmdb_format == IFD_ODR_CMD_IFD_ODR_DM_EXT_FMT)) ? 1'b1 : 1'b0;

  always_comb begin : p_req_ctrl
    // default:
    state_d = state_q;
    state_en = '0;
    req_cnt_start = 1'b0;
    req_cnt_incr = 1'b0;
    resp_cnt_start = 1'b0;

    defmem_rvld = 1'b0;

    cmdb_cmd_en = 1'b0;

    cmdb_rdy = ag_rdy;
    ag_vld = cmdb_cmd_vld_q;

    case (state_q)
      IDLE: begin

        cmdb_cmd_en = cmdb_vld;

        if (cmdb_format_lm & cmdb_vld) begin
          state_en = 1'b1;
          cmdb_rdy = 1'b1;
          ag_vld = 1'b0;

          req_cnt_start = 1'b1;
          resp_cnt_start = 1'b1;
          state_d = LOOP_FORM;
        end
      end
      LOOP_FORM: begin
        ag_vld = 1'b0;
        cmdb_rdy = 1'b0;

        defmem_rvld = 1'b1;  // request memory content
        req_cnt_incr = defmem_rrdy;  // increase request counter when memory is ready

        if (defmem_rrdy && (req_cnt_d == {cmd_numdim_p1, 1'b0})) begin
          state_en = 1'b1;
          state_d = LOOP_FINISH;
          req_cnt_incr = 1'b0;
        end
      end
      LOOP_FINISH: begin
        ag_vld   = 1'b0;
        cmdb_rdy = 1'b0;

        if (resp_cnt_q == {cmd_numdim_p1, 1'b0}) begin
          ag_vld = 1'b1;

          if (ag_rdy == 1'b1) begin
            state_en = 1'b1;
            state_d  = IDLE;
          end
        end
      end
      default: begin
        state_en = 1'b1;
        state_d  = IDLE;
      end
    endcase
  end

  // response control.
  // Increase response count and drive dim_def or loop_def when data is returned
  always_comb begin : p_resp_ctrl
    dim_def_en    = '0;
    loop_def_en   = '0;

    resp_cnt_incr = defmem_resp_vld;

    if (resp_dim_loop_n)
      dim_def_en[resp_cnt_q[1+:NUMDIM_PLUS_1_DW]] = defmem_resp_vld;
    else
      loop_def_en[resp_cnt_q[1+:NUMDIM_PLUS_1_DW]] = defmem_resp_vld;
  end

  // data muxing
  always_comb begin : p_data_mux
    // dim and loop def input select
    for (int i = 0; i < IFD_ODR_DEFMEM_MAX_LOOPS; i++) begin
      // default use memory response, correct one will be set by using the enable:
      dim_def_d[i]  = defmem_resp_data;
      loop_def_d[i] = defmem_resp_data;

      // reset to default values when starting
      if (resp_cnt_start) begin
        // as currently all dim en loop items have same default values between A B C and D, using just A for simplifying the loop/code
        dim_def_d[i][IFD_ODR_DEFMEM_DIM_W_LSB+:IFD_ODR_AG_DIM_W_A_DW] = IFD_ODR_AG_DIM_W_A_DEF_VAL;
        dim_def_d[i][IFD_ODR_DEFMEM_DIM_OFF_LSB+:IFD_ODR_AG_DIM_OFF_A_DW] = IFD_ODR_AG_DIM_OFF_A_DEF_VAL;
        dim_def_d[i][IFD_ODR_DEFMEM_MEM_STRIDE_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW] = IFD_ODR_AG_MEM_STRIDE_A_DEF_VAL;

        loop_def_d[i][IFD_ODR_DEFMEM_INNER_LEN_LSB+:IFD_ODR_AG_INNER_LEN_A_DW] = IFD_ODR_AG_INNER_LEN_A_DEF_VAL;
        loop_def_d[i][IFD_ODR_DEFMEM_INNER_STR_LSB+:IFD_ODR_AG_INNER_STR_A_DW] = IFD_ODR_AG_INNER_STR_A_DEF_VAL;
        loop_def_d[i][IFD_ODR_DEFMEM_OUTER_LEN_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW] = IFD_ODR_AG_OUTER_LEN_A_DEF_VAL;
        loop_def_d[i][IFD_ODR_DEFMEM_OUTER_STR_LSB+:IFD_ODR_AG_OUTER_STR_A_DW] = IFD_ODR_AG_OUTER_STR_A_DEF_VAL;
      end
    end

    // output select:
  end

  assign cmdb_cmd_vld_set = cmdb_vld & cmdb_rdy;
  assign cmdb_cmd_vld_clr = ag_vld & ag_rdy;
  assign cmdb_cmd_vld_en  = cmdb_cmd_vld_set | cmdb_cmd_vld_clr;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : p_ctrl_seq
    if (i_rst_n == 1'b0) begin
      state_q <= IDLE;
      req_cnt_q <= '0;
      resp_cnt_q <= '0;
      cmdb_cmd_vld_q <= '0;
    end else begin
      if (cmdb_cmd_vld_en) cmdb_cmd_vld_q <= cmdb_cmd_vld_set;

      if (state_en) state_q <= state_d;

      if (req_cnt_en) req_cnt_q <= req_cnt_d;

      if (resp_cnt_en) resp_cnt_q <= resp_cnt_d;
    end
  end

  // no reset needed for the data, control doesn't depend on the contents without the valid
  //spyglass disable_block STARC05-3.3.1.4b
  //spyglass disable_block STARC-2.3.4.3
  always_ff @(posedge i_clk) begin : p_data_seq
    if (cmdb_cmd_en) begin
      cmdb_cmd_q <= {cmdb_format, cmdb_cmd};
      cmdb_config_q <= cmdb_config;
    end

    for (int i = 0; i < IFD_ODR_DEFMEM_MAX_LOOPS; i++) begin
      if (dim_def_en[i] | resp_cnt_start) dim_def_q[i] <= dim_def_d[i];
      if (loop_def_en[i] | resp_cnt_start) loop_def_q[i] <= loop_def_d[i];
    end
  end
  //spyglass enable_block STARC-2.3.4.3
  //spyglass enable_block STARC05-3.3.1.4b

  assign {ag_format, ag_cmd_pre_ext} = cmdb_cmd_q;

  assign ag_config = cmdb_config_q;

  assign ag_cmd[IFD_ODR_CMDB_MAX_CMD_DW-1:0] = ag_cmd_pre_ext;
  // dim def A
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_W_A_LSB+:IFD_ODR_AG_DIM_W_A_DW] = dim_def_q[0][IFD_ODR_DEFMEM_DIM_W_LSB+:IFD_ODR_AG_DIM_W_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_OFF_A_LSB+:IFD_ODR_AG_DIM_OFF_A_DW] = dim_def_q[0][IFD_ODR_DEFMEM_DIM_OFF_LSB+:IFD_ODR_AG_DIM_OFF_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_STRIDE_A_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW] = dim_def_q[0][IFD_ODR_DEFMEM_MEM_STRIDE_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW];
  // dim def B
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_W_B_LSB+:IFD_ODR_AG_DIM_W_A_DW] = dim_def_q[1][IFD_ODR_DEFMEM_DIM_W_LSB+:IFD_ODR_AG_DIM_W_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_OFF_B_LSB+:IFD_ODR_AG_DIM_OFF_A_DW] = dim_def_q[1][IFD_ODR_DEFMEM_DIM_OFF_LSB+:IFD_ODR_AG_DIM_OFF_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_STRIDE_B_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW] = dim_def_q[1][IFD_ODR_DEFMEM_MEM_STRIDE_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW];
  // dim def C
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_W_C_LSB+:IFD_ODR_AG_DIM_W_A_DW] = dim_def_q[2][IFD_ODR_DEFMEM_DIM_W_LSB+:IFD_ODR_AG_DIM_W_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_OFF_C_LSB+:IFD_ODR_AG_DIM_OFF_A_DW] = dim_def_q[2][IFD_ODR_DEFMEM_DIM_OFF_LSB+:IFD_ODR_AG_DIM_OFF_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_STRIDE_C_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW] = dim_def_q[2][IFD_ODR_DEFMEM_MEM_STRIDE_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW];
  // dim def D
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_W_D_LSB+:IFD_ODR_AG_DIM_W_A_DW] = dim_def_q[3][IFD_ODR_DEFMEM_DIM_W_LSB+:IFD_ODR_AG_DIM_W_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_DIM_OFF_D_LSB+:IFD_ODR_AG_DIM_OFF_A_DW] = dim_def_q[3][IFD_ODR_DEFMEM_DIM_OFF_LSB+:IFD_ODR_AG_DIM_OFF_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_STRIDE_D_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW] = dim_def_q[3][IFD_ODR_DEFMEM_MEM_STRIDE_LSB+:IFD_ODR_AG_MEM_STRIDE_A_DW];
  // loop def A
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_LEN_A_LSB+:IFD_ODR_AG_INNER_LEN_A_DW] = loop_def_q[0][IFD_ODR_DEFMEM_INNER_LEN_LSB+:IFD_ODR_AG_INNER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_STR_A_LSB+:IFD_ODR_AG_INNER_STR_A_DW] = loop_def_q[0][IFD_ODR_DEFMEM_INNER_STR_LSB+:IFD_ODR_AG_INNER_STR_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_LEN_A_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW] = loop_def_q[0][IFD_ODR_DEFMEM_OUTER_LEN_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_STR_A_LSB+:IFD_ODR_AG_OUTER_STR_A_DW] = loop_def_q[0][IFD_ODR_DEFMEM_OUTER_STR_LSB+:IFD_ODR_AG_OUTER_STR_A_DW];
  // loop def B
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_LEN_B_LSB+:IFD_ODR_AG_INNER_LEN_A_DW] = loop_def_q[1][IFD_ODR_DEFMEM_INNER_LEN_LSB+:IFD_ODR_AG_INNER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_STR_B_LSB+:IFD_ODR_AG_INNER_STR_A_DW] = loop_def_q[1][IFD_ODR_DEFMEM_INNER_STR_LSB+:IFD_ODR_AG_INNER_STR_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_LEN_B_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW] = loop_def_q[1][IFD_ODR_DEFMEM_OUTER_LEN_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_STR_B_LSB+:IFD_ODR_AG_OUTER_STR_A_DW] = loop_def_q[1][IFD_ODR_DEFMEM_OUTER_STR_LSB+:IFD_ODR_AG_OUTER_STR_A_DW];
  // loop def C
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_LEN_C_LSB+:IFD_ODR_AG_INNER_LEN_A_DW] = loop_def_q[2][IFD_ODR_DEFMEM_INNER_LEN_LSB+:IFD_ODR_AG_INNER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_STR_C_LSB+:IFD_ODR_AG_INNER_STR_A_DW] = loop_def_q[2][IFD_ODR_DEFMEM_INNER_STR_LSB+:IFD_ODR_AG_INNER_STR_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_LEN_C_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW] = loop_def_q[2][IFD_ODR_DEFMEM_OUTER_LEN_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_STR_C_LSB+:IFD_ODR_AG_OUTER_STR_A_DW] = loop_def_q[2][IFD_ODR_DEFMEM_OUTER_STR_LSB+:IFD_ODR_AG_OUTER_STR_A_DW];
  // loop def D
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_LEN_D_LSB+:IFD_ODR_AG_INNER_LEN_A_DW] = loop_def_q[3][IFD_ODR_DEFMEM_INNER_LEN_LSB+:IFD_ODR_AG_INNER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_INNER_STR_D_LSB+:IFD_ODR_AG_INNER_STR_A_DW] = loop_def_q[3][IFD_ODR_DEFMEM_INNER_STR_LSB+:IFD_ODR_AG_INNER_STR_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_LEN_D_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW] = loop_def_q[3][IFD_ODR_DEFMEM_OUTER_LEN_LSB+:IFD_ODR_AG_OUTER_LEN_A_DW];
  assign ag_cmd[IFD_ODR_DM_BASE_OUTER_STR_D_LSB+:IFD_ODR_AG_OUTER_STR_A_DW] = loop_def_q[3][IFD_ODR_DEFMEM_OUTER_STR_LSB+:IFD_ODR_AG_OUTER_STR_A_DW];


  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
  property p_vld_deassrtion_on_rdy(i_clk, i_rst_n, vld, rdy);
    @(posedge i_clk) disable iff (!i_rst_n) vld & ~rdy |=> vld;
  endproperty

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, cmdb_vld, cmdb_rdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, ag_vld, ag_rdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, defmem_rvld, defmem_rrdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule

`endif  // _IFD_LOOP_UNROLL_SV_
