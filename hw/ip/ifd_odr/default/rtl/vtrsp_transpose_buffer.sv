// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Transpose buffer for the vtrsp
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _VTRSP_TRANSPOSE_BUFFER_SV_
`define _VTRSP_TRANSPOSE_BUFFER_SV_

module vtrsp_transpose_buffer #(
  parameter int unsigned EL_SIZE = 8,
  parameter int unsigned NR_EL   = 64
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic i_fill_connection,
  input logic i_drain_connection,

  input logic [$bits(vtrsp_pkg::vtrsp_cmd_mode_e)-1:0] i_fill_cmd_mode,
  input logic [$bits(vtrsp_pkg::vtrsp_cmd_mode_e)-1:0] i_drain_cmd_mode,

  input logic [NR_EL-1:0][EL_SIZE-1:0] i_inp_dat,
  input logic [NR_EL-1:0]              i_inp_en,

  input  logic [NR_EL-1:0]              i_outp_en,
  output logic [NR_EL-1:0][EL_SIZE-1:0] o_outp_dat
);

  logic [EL_SIZE-1:0] col_min_1_dat[NR_EL][NR_EL];
  logic [EL_SIZE-1:0] col_dat      [NR_EL][NR_EL];

  logic [EL_SIZE-1:0] row_min_1_dat[NR_EL][NR_EL];
  logic [EL_SIZE-1:0] row_dat      [NR_EL][NR_EL];

  for (genvar row = 0; unsigned'(row) < NR_EL; row++) begin: g_row
    for (genvar col = 0; unsigned'(col) < NR_EL; col++) begin: g_col
      logic inp_en;
      logic outp_en;

      always_comb begin
        inp_en = 0;
        outp_en = 0;

        if ((i_fill_cmd_mode == vtrsp_pkg::fp8_mode) ||
            ((i_fill_cmd_mode == vtrsp_pkg::fp16_mode) && ((row % 2) == (col % 2))) || // only the diagonal needs to be stored
            ((i_fill_cmd_mode == vtrsp_pkg::fp32_mode) && ((row % 4) == (col % 4)))    // only the diagonal needs to be stored
        ) begin
          if (i_fill_connection == vtrsp_pkg::ROW)
            inp_en = i_inp_en[row];
          else
            inp_en = i_inp_en[col];
        end

        if ((i_drain_cmd_mode == vtrsp_pkg::fp8_mode) ||
            ((i_drain_cmd_mode == vtrsp_pkg::fp16_mode) && ((row % 2) == (col % 2))) || // only the diagonal needs to be stored
            ((i_drain_cmd_mode == vtrsp_pkg::fp32_mode) && ((row % 4) == (col % 4)))    // only the diagonal needs to be stored
        ) begin
          if (i_drain_connection == vtrsp_pkg::COLUMN)
            outp_en = i_outp_en[col];
          else
            outp_en = i_outp_en[row];
        end
      end

      vtrsp_transpose_buffer_el_cell #(
        .EL_SIZE(EL_SIZE)
      ) el_cell (
        .i_clk  (i_clk),
        .i_rst_n(i_rst_n),

        .i_inp_row_dat(i_fill_connection == vtrsp_pkg::ROW    ? i_inp_dat[col] : '0), // each row gets the same data
        .i_inp_col_dat(i_fill_connection == vtrsp_pkg::COLUMN ? i_inp_dat[row] : '0), // each column gets the same data

        .i_inp_row_en(i_fill_connection == vtrsp_pkg::ROW    ? inp_en : '0), // each column gets the same enable
        .i_inp_col_en(i_fill_connection == vtrsp_pkg::COLUMN ? inp_en : '0), // each row gets sthe same enable

          // output is transposed, so output column when mode is fill with row and the other way around
        .i_outp_col_en (i_drain_connection == vtrsp_pkg::COLUMN ? outp_en : '0), // each row gets the same enable
        .i_outp_row_en (i_drain_connection == vtrsp_pkg::ROW    ? outp_en : '0), // each column gets the same enable

        .i_col_min_1_dat(col_min_1_dat[col][row]),
        .i_row_min_1_dat(row_min_1_dat[row][col]),

        .o_outp_col_dat(col_dat[col][row]),
        .o_outp_row_dat(row_dat[row][col])
      );
    end
  end
  always_comb begin
    for (int unsigned idx=0; idx<NR_EL; idx++) begin
      // min_1 assignments:
      if (idx == 0) begin
        col_min_1_dat[idx] = '{default:'0};
        row_min_1_dat[idx] = '{default:'0};
      end else begin
        col_min_1_dat[idx] = col_dat[idx-1];
        row_min_1_dat[idx] = row_dat[idx-1];
      end

      // output driver:
      if(i_drain_connection == vtrsp_pkg::COLUMN)
        o_outp_dat[idx] = col_dat[NR_EL-1][idx];
      else
        o_outp_dat[idx] = row_dat[NR_EL-1][idx];
    end
  end

endmodule

module vtrsp_transpose_buffer_el_cell #(
  parameter int unsigned EL_SIZE = 8
) (
  input  wire i_clk,
  input  wire i_rst_n,

  input  logic [EL_SIZE-1:0]  i_inp_row_dat,
  input  logic [EL_SIZE-1:0]  i_inp_col_dat,

  input  logic                i_inp_row_en,
  input  logic                i_inp_col_en,

  input  logic                i_outp_col_en,
  input  logic                i_outp_row_en,
  input  logic [EL_SIZE-1:0]  i_col_min_1_dat,
  input  logic [EL_SIZE-1:0]  i_row_min_1_dat,
  output logic [EL_SIZE-1:0]  o_outp_col_dat,
  output logic [EL_SIZE-1:0]  o_outp_row_dat
);
  reg [EL_SIZE-1:0] cell_q;
  logic [EL_SIZE-1:0] cell_in;
  logic cell_en;

  always_comb begin
    if (i_inp_row_en)
      cell_in = i_inp_row_dat;
    else if (i_inp_col_en)
      cell_in = i_inp_col_dat;
    else
      cell_in = '0;
  end

  always_comb begin
    if (i_outp_row_en)
      o_outp_row_dat = cell_q;
    else
      o_outp_row_dat = i_row_min_1_dat;

    if (i_outp_col_en)
      o_outp_col_dat = cell_q;
    else
      o_outp_col_dat = i_col_min_1_dat;
  end

  always_comb cell_en  = i_inp_row_en | i_inp_col_en;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : cell_reg
    if (i_rst_n == 0) cell_q <= '0;
    else if (cell_en) cell_q <= cell_in;
  end

endmodule

`endif  // _TRANSPOSE_BUFFER_SV_
