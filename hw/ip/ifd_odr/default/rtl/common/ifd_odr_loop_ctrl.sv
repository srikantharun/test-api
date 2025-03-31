// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Control implementing the nested for-loops and firing the multiply incrementers
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_LOOP_CTRL_SV_
`define _IFD_ODR_LOOP_CTRL_SV_

`ifndef IFD_ODR_MAX
`define IFD_ODR_MAX(a, b) ((a)>(b)?(a):(b))
`endif
`ifndef IFD_ODR_MIN
`define IFD_ODR_MIN(a, b) ((a)<(b)?(a):(b))
`endif

`define IFD_ODR_CIDX_ADDR_LAT 1
`define IFD_ODR_OTHER_ADDR_LAT 4

module ifd_odr_loop_ctrl
  import ifd_odr_pkg::*;
#(
  parameter type cmdgen_status_reg_t = logic
) (
  input wire i_clk,
  input wire i_rst_n,

  input  logic start,
  output logic busy,
  output logic pipe_en,
  output logic last,

  input logic [IFD_ODR_AG_OUTER_LEN_A_DW-1:0] outer_len_a,
  input logic [IFD_ODR_AG_OUTER_LEN_B_DW-1:0] outer_len_b,
  input logic [IFD_ODR_AG_OUTER_LEN_C_DW-1:0] outer_len_c,
  input logic [IFD_ODR_AG_OUTER_LEN_D_DW-1:0] outer_len_d,
  input logic [IFD_ODR_AG_INNER_LEN_A_DW-1:0] inner_len_a,
  input logic [IFD_ODR_AG_INNER_LEN_B_DW-1:0] inner_len_b,
  input logic [IFD_ODR_AG_INNER_LEN_C_DW-1:0] inner_len_c,
  input logic [IFD_ODR_AG_INNER_LEN_D_DW-1:0] inner_len_d,

  output logic outer_a_incr,
  output logic outer_a_set0,
  output logic outer_b_incr,
  output logic outer_b_set0,
  output logic outer_c_incr,
  output logic outer_c_set0,
  output logic outer_d_incr,
  output logic outer_d_set0,
  output logic inner_a_incr,
  output logic inner_a_set0,
  output logic inner_b_incr,
  output logic inner_b_set0,
  output logic inner_c_incr,
  output logic inner_c_set0,
  output logic inner_d_incr,
  output logic inner_d_set0,

  output logic addr_vld,
  input  logic addr_rdy,

  output cmdgen_status_reg_t cmdgen_status
);

  localparam int unsigned CtrlLat = IFD_ODR_TOT_LATENCY - 1;
  typedef enum reg [1:0] {
    IDLE = 2'b00,
    START = 2'b01,
    IN_LOOP = 2'b10,
    END_LOOP = 2'b11
  } state_t;
  state_t cur_state, nxt_state;

  reg [CtrlLat-1:0] addr_lat;
  reg [CtrlLat-1:0] last_lat;
  logic addr_lat_in;
  logic last_lat_in;

  logic outp_vld;

  logic start_loop;
  logic loop_running;
  logic stall;
  logic loop_finished;

  logic outer_a_decr;
  logic outer_b_decr;
  logic outer_c_decr;
  logic outer_d_decr;
  logic inner_a_decr;
  logic inner_b_decr;
  logic inner_c_decr;
  logic inner_d_decr;

  logic outer_a_zero;
  logic outer_b_zero;
  logic outer_c_zero;
  logic outer_d_zero;
  logic inner_a_zero;
  logic inner_b_zero;
  logic inner_c_zero;
  logic inner_d_zero;

  // connect decrements:
  assign outer_a_decr = outer_b_zero & outer_b_decr;
  assign outer_b_decr = outer_c_zero & outer_c_decr;
  assign outer_c_decr = outer_d_zero & outer_d_decr;
  assign outer_d_decr = inner_a_zero & inner_a_decr;
  assign inner_a_decr = inner_b_zero & inner_b_decr;
  assign inner_b_decr = inner_c_zero & inner_c_decr;
  assign inner_c_decr = inner_d_zero & inner_d_decr;
  assign inner_d_decr = loop_running & ~stall;

  assign pipe_en = busy & ~stall;

  always_comb begin : ctrl_fsm
    nxt_state    = cur_state;
    start_loop   = 1'b0;
    addr_lat_in  = 1'b0;
    loop_running = 1'b0;
    busy         = 1'b0;

    unique case (cur_state)
      IDLE: begin
        if (start == 1'b1) begin
          nxt_state = START;
        end
      end
      START: begin
        start_loop = 1'b1;
        busy       = 1'b1;
        nxt_state  = IN_LOOP;
      end
      IN_LOOP: begin
        busy         = 1'b1;
        addr_lat_in  = 1'b1;
        loop_running = 1'b1;

        if (loop_finished && ~stall) nxt_state = END_LOOP;
      end
      END_LOOP: begin
        busy        = 1'b1;
        addr_lat_in = 1'b0;
        if (addr_lat == '0)  // nothing in the pipe
          nxt_state = IDLE;
      end
      default: nxt_state = IDLE;
    endcase
  end

  assign stall = outp_vld & ~addr_rdy;
  assign loop_finished = inner_d_zero & inner_c_zero & inner_b_zero & inner_a_zero &
                           outer_d_zero & outer_c_zero & outer_b_zero & outer_a_zero;
  assign outp_vld = addr_lat[0];
  assign last = last_lat[0];
  assign addr_vld = outp_vld;
  assign last_lat_in = loop_finished;

  // the sequential part:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : regs
    if (!i_rst_n) begin
      cur_state <= IDLE;
      addr_lat  <= '0;
      last_lat  <= '0;
    end else begin
      if (cur_state != nxt_state) cur_state <= nxt_state;

      // latency regs only when in loop and not stalling:
      if((cur_state inside {IN_LOOP, END_LOOP}) && !stall) begin
        addr_lat <= {addr_lat_in, addr_lat[CtrlLat-1:1]};
        last_lat <= {last_lat_in, last_lat[CtrlLat-1:1]};
      end
    end
  end

  ///////////////////////////////////////
  // loop counters:
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_INNER_LEN_D_DW)
  ) u_inner_d_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(inner_d_decr),
    .cfg_val(inner_len_d),
    .zero(inner_d_zero),

    .mul_incr(inner_d_incr),
    .mul_set0(inner_d_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_INNER_LEN_C_DW)
  ) u_inner_c_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(inner_c_decr),
    .cfg_val(inner_len_c),
    .zero(inner_c_zero),

    .mul_incr(inner_c_incr),
    .mul_set0(inner_c_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_INNER_LEN_B_DW)
  ) u_inner_b_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(inner_b_decr),
    .cfg_val(inner_len_b),
    .zero(inner_b_zero),

    .mul_incr(inner_b_incr),
    .mul_set0(inner_b_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_INNER_LEN_A_DW)
  ) u_inner_a_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(inner_a_decr),
    .cfg_val(inner_len_a),
    .zero(inner_a_zero),

    .mul_incr(inner_a_incr),
    .mul_set0(inner_a_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_OUTER_LEN_D_DW)
  ) u_outer_d_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(outer_d_decr),
    .cfg_val(outer_len_d),
    .zero(outer_d_zero),

    .mul_incr(outer_d_incr),
    .mul_set0(outer_d_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_OUTER_LEN_C_DW)
  ) u_outer_c_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(outer_c_decr),
    .cfg_val(outer_len_c),
    .zero(outer_c_zero),

    .mul_incr(outer_c_incr),
    .mul_set0(outer_c_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_OUTER_LEN_B_DW)
  ) u_outer_b_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(outer_b_decr),
    .cfg_val(outer_len_b),
    .zero(outer_b_zero),

    .mul_incr(outer_b_incr),
    .mul_set0(outer_b_set0)
  );
  ifd_odr_loop_cnt #(
    .VAL_W(IFD_ODR_AG_OUTER_LEN_A_DW)
  ) u_outer_a_cnt (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .start(start_loop),
    .decr(outer_a_decr),
    .cfg_val(outer_len_a),
    .zero(outer_a_zero),

    .mul_incr(outer_a_incr),
    .mul_set0(outer_a_set0)
  );
  ///////////////////////////////////////

  ///////////////////////////////////////
  // State observation
  assign cmdgen_status = '{
          fsm_state: '{d: cur_state},
          instr_stalled: '{d: stall},
          out_a_zero: '{d: outer_a_zero},
          out_b_zero: '{d: outer_b_zero},
          out_c_zero: '{d: outer_c_zero},
          out_d_zero: '{d: outer_d_zero},
          inner_a_zero: '{d: inner_a_zero},
          inner_b_zero: '{d: inner_b_zero},
          inner_c_zero: '{d: inner_c_zero},
          inner_d_zero: '{d: inner_d_zero}
      };
endmodule

`endif  // _IFD_ODR_LOOP_CTRL_SV_
