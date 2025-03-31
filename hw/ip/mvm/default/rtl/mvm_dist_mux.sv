// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_DIST_MUX_SV
`define MVM_DIST_MUX_SV

module mvm_dist_mux
  import imc_bank_pkg::*;
  import mvm_pkg::*;
#(
  parameter int unsigned OR_DATA = 0,
  parameter bit IN1_PIPELINE_EN = 1'b0,
  parameter bit OUT_PIPELINE_EN = 1'b0
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] in_0,
  input compute_out_ctrl_t in_0_ctrl,
  input logic in_0_valid,

  input logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] in_1,
  input compute_out_ctrl_t in_1_ctrl,
  input logic in_1_valid,

  output logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] out_data,
  output compute_out_ctrl_t out_ctrl,
  output logic out_valid

);

  logic                                                int_in1_valid;
  compute_out_ctrl_t                                   int_in1_ctrl;
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] int_in1_data;

  logic                                                int_out_valid;
  compute_out_ctrl_t                                   int_out_ctrl;
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] int_out_data;

  if(IN1_PIPELINE_EN) begin : g_in1_pipeline
    always_ff @(posedge i_clk, negedge i_rst_n)
      if(!i_rst_n)                        int_in1_valid <= 1'b0;
      else if(int_in1_valid ^ in_1_valid) int_in1_valid <= in_1_valid;

    always_ff @(posedge i_clk, negedge i_rst_n)
      if(!i_rst_n)          int_in1_ctrl <= '0;
      else begin
             if(in_1_valid) int_in1_ctrl <= in_1_ctrl;
        else if(OR_DATA)    int_in1_ctrl <= '0;
      end
  end else begin : g_no_in1_pipeline
    always_comb begin
      int_in1_valid = in_1_valid;
      int_in1_ctrl  = in_1_ctrl;
    end
  end

  assign int_out_valid = in_0_valid | int_in1_valid;

  // MUX for the tlast bit of the output stream
  mvm_dist_mux_single_out #(
    .OR_DATA(OR_DATA),
    .DATA_WIDTH($bits(compute_out_ctrl_t))
  ) inst_mvm_dist_mux_last (
    .in_0(in_0_ctrl),
    .in_0_valid(in_0_valid),
    .in_1(int_in1_ctrl),
    .in_1_valid(int_in1_valid),
    .out_data(int_out_ctrl)
  );

  // Individual MUXes for each output column of the IMC bank. Having an instance per column aids the structured place and route.
  for (genvar g = 0; g < IMC_NB_COLS_PER_BANK; g++) begin : g_mvm_dist_muxes_per_output
    if(IN1_PIPELINE_EN) begin : g_in1_data_pipeline
      always_ff @(posedge i_clk)
             if(in_1_valid) int_in1_data[g] <= in_1[g];
        else if(OR_DATA)    int_in1_data[g] <= '0;
    end else begin : g_in1_data_no_pipeline
      assign int_in1_data[g] = in_1[g];
    end

    mvm_dist_mux_single_out #(
      .OR_DATA(OR_DATA),
      .DATA_WIDTH(MVM_OUT_DATA_W)
    ) inst_mvm_dist_mux_single_out (
      .in_0(in_0[g]),
      .in_0_valid(in_0_valid),
      .in_1(int_in1_data[g]),
      .in_1_valid(int_in1_valid),
      .out_data(int_out_data[g])
    );

    if(OUT_PIPELINE_EN) begin : g_out_data_pipeline
      // Output data must be sanitized because downstream muxes have OR_DATA == 1
      always_ff @(posedge i_clk, negedge i_rst_n)
        if(!i_rst_n)        out_data[g] <= '0;
        else begin
          if(int_out_valid) out_data[g] <= int_out_data[g];
          else              out_data[g] <= '0;
        end
    end else begin : g_out_data_no_pipeline
      assign out_data[g] = int_out_data[g];
    end
  end

  if(OUT_PIPELINE_EN) begin : g_out_pipeline
    always_ff @(posedge i_clk, negedge i_rst_n)
      if(!i_rst_n)                        out_valid <= 1'b0;
      else if(^{out_valid,int_out_valid}) out_valid <= int_out_valid;

    always_ff @(posedge i_clk, negedge i_rst_n)
      if(!i_rst_n)        out_ctrl <= '0;
      else begin
        if(int_out_valid) out_ctrl <= int_out_ctrl;
        else              out_ctrl <= '0;
      end
  end else begin : g_no_out_pipeline
    always_comb begin
      out_valid = int_out_valid;
      out_ctrl  = int_out_ctrl;
    end
  end


endmodule

`endif  // MVM_DIST_MUX_SV
