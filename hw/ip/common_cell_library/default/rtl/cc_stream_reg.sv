// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// Register with a simple stream-like ready/valid handshake.
/// This register does not cut combinatorial paths on all control signals; if you need a complete
/// cut, use the `spill_register`.
module cc_stream_reg #(
  /// The data width of the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth      = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type         data_t         = logic [DataWidth-1:0],
  /// Data FFs can be made non-resettable to save on reset network routing for wide data regs
  parameter bit          DataRegNoReset = 1'b0
) (
  /// Clock, positive edge triggered
  input  wire   i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  // doc sync i_clk
  /// Flush any active saved data
  input  logic  i_flush,
  /// The input data
  input  data_t i_data,
  /// Valid from the input stream
  input  logic  i_valid,
  /// Ready from the input stream
  output logic  o_ready,
  /// the output data
  output data_t o_data,
  /// Valid of the output stream
  output logic  o_valid,
  /// Ready from the output stream
  input  logic  i_ready
);

  logic reg_ena;
  assign o_ready = i_ready | ~o_valid;
  assign reg_ena = i_valid & o_ready;

  // FFLARNC: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
`ifndef NO_SYNOPSYS_FF
  /* synopsys sync_set_reset "i_flush" */
`endif
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) o_valid <= '0;
    else if (i_flush) o_valid <= '0;
    else if (o_ready) o_valid <= i_valid;
  end

  if (DataRegNoReset) begin : gen_non_rst_regs
    // FFLNR: D-Flip-Flop, load enable, no reset
    always_ff @(posedge i_clk) begin
      if (reg_ena) o_data <= i_data;
    end
  end else begin : gen_rst_regs
    // FFL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) o_data <= data_t'(0);
      else if (reg_ena) o_data <= i_data;
    end
  end

endmodule
