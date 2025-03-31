// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Intermediate unit between performance tracking CSRs and AI Core subips.
// Width of internal adders can be configured to reduce footprint.
// Stall counters can be enabled separately for each interface.
// Owner: Gua Hao Khov <guahao.khov@axelera.ai>

`ifndef PERF_TRACKER_SV
`define PERF_TRACKER_SV

// verilog_lint: waive-start line-length
module perf_tracker #(
  parameter int unsigned DATA_W = 32,
  parameter int unsigned CNTR_W = 32,
  parameter int unsigned IN0_EN = 1,
  parameter int unsigned IN1_EN = 1,
  parameter int unsigned OUT_EN = 1
) (
  input wire i_clk,
  input logic i_rst_n,
  // cmdblock state signals
  input logic cmdblock_busy_i,
  input logic cmdblock_wait_token_i,
  // interface stall signals
  input logic in0_stall_i,
  input logic in1_stall_i,
  input logic out_stall_i,
  // perf CSR enable signals
  input logic csr_busy_state_en_i,
  input logic csr_idle_state_en_i,
  input logic csr_token_stall_en_i,
  input logic csr_io_stall_en_i,
  input logic csr_in0_stall_en_i,
  input logic csr_in1_stall_en_i,
  input logic csr_out_stall_en_i,
  // perf CSR current value signals
  input logic [DATA_W-1:0] csr_busy_state_curr_i,
  input logic [DATA_W-1:0] csr_idle_state_curr_i,
  input logic [DATA_W-1:0] csr_token_stall_curr_i,
  input logic [DATA_W-1:0] csr_io_stall_curr_i,
  input logic [DATA_W-1:0] csr_in0_stall_curr_i,
  input logic [DATA_W-1:0] csr_in1_stall_curr_i,
  input logic [DATA_W-1:0] csr_out_stall_curr_i,
  // perf CSR next value signals
  output logic [DATA_W-1:0] csr_busy_state_next_o,
  output logic [DATA_W-1:0] csr_idle_state_next_o,
  output logic [DATA_W-1:0] csr_token_stall_next_o,
  output logic [DATA_W-1:0] csr_io_stall_next_o,
  output logic [DATA_W-1:0] csr_in0_stall_next_o,
  output logic [DATA_W-1:0] csr_in1_stall_next_o,
  output logic [DATA_W-1:0] csr_out_stall_next_o,
  // perf CSR write enable signals
  output logic csr_busy_state_we_o,
  output logic csr_idle_state_we_o,
  output logic csr_token_stall_we_o,
  output logic csr_io_stall_we_o,
  output logic csr_in0_stall_we_o,
  output logic csr_in1_stall_we_o,
  output logic csr_out_stall_we_o
);

  // verilog_lint: waive-start generate-label-prefix
  // auxiliary signals
  logic busy_state;
  logic idle_state;
  logic token_stall;
  logic io_stall;
  logic in0_stall;
  logic in1_stall;
  logic out_stall;

  // internal counter values
  logic [CNTR_W-1:0] idle_state_cntr;
  logic [CNTR_W-1:0] busy_state_cntr;
  logic [CNTR_W-1:0] token_stall_cntr;
  logic [CNTR_W-1:0] io_stall_cntr;
  logic [CNTR_W-1:0] in0_stall_cntr;
  logic [CNTR_W-1:0] in1_stall_cntr;
  logic [CNTR_W-1:0] out_stall_cntr;

  // auxiliary signals evaluation
  assign busy_state = cmdblock_busy_i;
  assign idle_state = ~cmdblock_busy_i;
  assign token_stall = idle_state & cmdblock_wait_token_i;
  assign io_stall = in0_stall | in1_stall | out_stall;

  // internal counter update
  assign busy_state_cntr = csr_busy_state_curr_i + 1'b1;
  assign idle_state_cntr = csr_idle_state_curr_i + 1'b1;
  assign token_stall_cntr = csr_token_stall_curr_i + 1'b1;
  assign io_stall_cntr = csr_io_stall_curr_i + 1'b1;

  // width conversion from internal counter to CSR
  assign csr_busy_state_next_o = DATA_W'(busy_state_cntr);
  assign csr_idle_state_next_o = DATA_W'(idle_state_cntr);
  assign csr_token_stall_next_o = DATA_W'(token_stall_cntr);
  assign csr_io_stall_next_o = DATA_W'(io_stall_cntr);

  // CSR write enable based on enable signal and state
  assign csr_busy_state_we_o = busy_state & csr_busy_state_en_i;
  assign csr_idle_state_we_o = idle_state & csr_idle_state_en_i;
  assign csr_token_stall_we_o = token_stall & csr_token_stall_en_i;
  assign csr_io_stall_we_o = io_stall & csr_io_stall_en_i;

  // conditional generation of interface stall counters
  if (IN0_EN != 0) begin : in0_stall_cntr_enabled
    assign in0_stall = in0_stall_i;
    assign in0_stall_cntr = csr_in0_stall_curr_i + 1'b1;
    assign csr_in0_stall_next_o = DATA_W'(in0_stall_cntr);
    assign csr_in0_stall_we_o = in0_stall & csr_in0_stall_en_i;
  end else begin : in0_stall_disabled
    assign in0_stall = 1'b0;
    assign in0_stall_cntr = 'b0;
    assign csr_in0_stall_next_o = 'b0;
    assign csr_in0_stall_we_o = 1'b0;
  end
  if (IN1_EN != 0) begin : in1_stall_cntr_enabled
    assign in1_stall = in1_stall_i;
    assign in1_stall_cntr = csr_in1_stall_curr_i + 1'b1;
    assign csr_in1_stall_next_o = DATA_W'(in1_stall_cntr);
    assign csr_in1_stall_we_o = in1_stall & csr_in1_stall_en_i;
  end else begin : in1_stall_disabled
    assign in1_stall = 1'b0;
    assign in1_stall_cntr = 'b0;
    assign csr_in1_stall_next_o = 'b0;
    assign csr_in1_stall_we_o = 1'b0;
  end
  if (OUT_EN != 0) begin : out_stall_cntr_enabled
    assign out_stall = out_stall_i;
    assign out_stall_cntr = csr_out_stall_curr_i + 1'b1;
    assign csr_out_stall_next_o = DATA_W'(out_stall_cntr);
    assign csr_out_stall_we_o = out_stall & csr_out_stall_en_i;
  end else begin : out_stall_disabled
    assign out_stall = 1'b0;
    assign out_stall_cntr = 'b0;
    assign csr_out_stall_next_o = 'b0;
    assign csr_out_stall_we_o = 1'b0;
  end

  /////////////
  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON

  // No CSR input should exceed the internal counter width
  property busy_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_busy_state_en_i |-> (csr_busy_state_curr_i < 2 ** CNTR_W);
  endproperty
  property idle_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_idle_state_en_i |-> (csr_idle_state_curr_i < 2 ** CNTR_W);
  endproperty
  property token_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_token_stall_en_i |-> (csr_token_stall_curr_i < 2 ** CNTR_W);
  endproperty
  property io_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_io_stall_en_i |-> (csr_io_stall_curr_i < 2 ** CNTR_W);
  endproperty
  property in0_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_in0_stall_en_i |-> (csr_in0_stall_curr_i < 2 ** CNTR_W);
  endproperty
  property in1_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_in1_stall_en_i |-> (csr_in1_stall_curr_i < 2 ** CNTR_W);
  endproperty
  property out_cntr_w;
    @(posedge i_clk) disable iff (!i_rst_n) csr_out_stall_en_i |-> (csr_out_stall_curr_i < 2 ** CNTR_W);
  endproperty

  assert property (busy_cntr_w)
  else $error("csr_busy_state_curr_i exceeds internal counter width!");

  assert property (idle_cntr_w)
  else $error("csr_idle_state_curr_i exceeds internal counter width!");

  assert property (token_cntr_w)
  else $error("csr_token_stall_curr_i exceeds internal counter width!");

  assert property (io_cntr_w)
  else $error("csr_io_stall_curr_i exceeds internal counter width!");

  assert property (in0_cntr_w)
  else $error("csr_in0_stall_curr_i exceeds internal counter width!");

  assert property (in1_cntr_w)
  else $error("csr_in1_stall_curr_i exceeds internal counter width!");

  assert property (out_cntr_w)
  else $error("csr_out_stall_curr_i exceeds internal counter width!");

`endif  // ASSERTIONS_ON
  //synopsys translate_on

  // verilog_lint: waive-stop generate-label-prefix
endmodule

// verilog_lint: waive-stop line-length
`endif  // PERF_TRACKER_SV
