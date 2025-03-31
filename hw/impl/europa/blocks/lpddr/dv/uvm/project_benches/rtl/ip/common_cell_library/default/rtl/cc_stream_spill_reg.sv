// Copyright 2021 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>


/// A register with handshakes that completely cuts any combinational paths
/// between the input and output. This spill register can be flushed.
module cc_stream_spill_reg #(
  /// Data Width, optional if `data_t` is used
  parameter int unsigned DataWidth      = 32,
  /// The actual data type used for the patload ports
  parameter type         data_t         = logic [DataWidth-1:0],
  /// This will not instantiate a register at all
  parameter bit          Bypass         = 1'b0,
  /// Have the data pipeline first, useful for partition input streams
  parameter bit          CutFirst       = 1'b0,
  /// Data FFs can be made non-resettable to save on reset network routing for wide data regs
  parameter bit          DataRegNoReset = 1'b0
) (
  /// Clock, positive edge triggered
  input  wire   i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  // doc sync i_clk
  /// Synchronously flush the registers
  input  logic  i_flush,
  /// Input stream payload data
  input  data_t i_data,
  /// Input stream is valid
  input  logic  i_valid,
  /// Input stream is ready
  output logic  o_ready,
  /// Output stream payload data
  output data_t o_data,
  /// Output stream payload is valid
  output logic  o_valid,
  /// Ouptu stream is ready
  input  logic  i_ready
);

  if (Bypass) begin : gen_bypass
    always_comb o_valid = i_valid;
    always_comb o_ready = i_ready;
    always_comb o_data = i_data;
  end : gen_bypass
  else if (CutFirst) begin : gen_spill_reg_front
    // The A register.
    data_t a_data_q;
    logic  a_full_q;
    logic a_fill, a_drain;

    if (DataRegNoReset) begin : gen_non_rst_a_regs
      always_ff @(posedge i_clk) begin : ps_a_data
        if (a_fill) a_data_q <= i_data;
      end
    end else begin : gen_rst_a_regs
      always_ff @(posedge i_clk or negedge i_rst_n) begin : ps_a_data
        if (!i_rst_n) a_data_q <= data_t'(0);
        else if (a_fill) a_data_q <= i_data;
      end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin : ps_a_full
      if (!i_rst_n) a_full_q <= 0;
      else if (a_fill || a_drain) a_full_q <= a_fill;
    end

    // The B register.
    data_t b_data_q;
    logic  b_full_q;
    logic b_fill, b_drain;

    if (DataRegNoReset) begin : gen_non_rst_b_regs
      always_ff @(posedge i_clk) begin : ps_b_data
        if (b_fill) b_data_q <= a_data_q;
      end
    end else begin : gen_rst_b_regs
      always_ff @(posedge i_clk or negedge i_rst_n) begin : ps_b_data
        if (!i_rst_n) b_data_q <= data_t'(0);
        else if (b_fill) b_data_q <= a_data_q;
      end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin : ps_b_full
      if (!i_rst_n) b_full_q <= 0;
      else if (b_fill || b_drain) b_full_q <= b_fill;
    end

    // Fill the A register when the A or B register is empty. Drain the A register
    // whenever it is full and being filled, or if a flush is requested.
    always_comb a_fill = i_valid && o_ready && (!i_flush);
    always_comb a_drain = (a_full_q && !b_full_q) || i_flush;

    // Fill the B register whenever the A register is drained, but the downstream
    // circuit is not ready. Drain the B register whenever it is full and the
    // downstream circuit is ready, or if a flush is requested.
    always_comb b_fill = a_drain && (!i_ready) && (!i_flush);
    always_comb b_drain = (b_full_q && i_ready) || i_flush;

    // We can accept input as long as register B is not full.
    // Note: i_flush and i_valid must not be high at the same time,
    // otherwise an invalid handshake may occur
    always_comb o_ready = !a_full_q || !b_full_q;

    // The unit provides output as long as one of the registers is filled.
    always_comb o_valid = a_full_q | b_full_q;

    // We empty the spill register before the slice register.
    always_comb o_data = b_full_q ? b_data_q : a_data_q;

  end : gen_spill_reg_front
  else begin : gen_spill_reg_back
    /////////////////////
    // Bypass Register //
    /////////////////////
    data_t bypass_data_q;
    logic  bypass_load;
    logic bypass_valid_q, bypass_clear, bypass_set;

    ///////////////////////
    // Pipeline register //
    ///////////////////////
    data_t pipeline_data_q, pipeline_data_d;
    logic pipeline_load;
    logic pipeline_valid_q, pipeline_clear, pipeline_set;

    //////////////////////////
    // Internal handshaking //
    //////////////////////////
    logic internal_valid, internal_ready;

    always_comb internal_valid = i_valid | bypass_valid_q;
    always_comb internal_ready = ~pipeline_valid_q | i_ready;

    ////////////////////////////////////
    // Bypass Register, Control RS FF //
    ////////////////////////////////////
    always_comb bypass_clear = internal_ready;
    always_comb bypass_set = i_valid;

`ifndef NO_SYNOPSYS_FF
  /* synopsys sync_set_reset "i_flush" */
`endif
    // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) bypass_valid_q <= 1'b0;
      else if (i_flush) bypass_valid_q <= 1'b0;
      else if (bypass_clear) bypass_valid_q <= 1'b0;
      else if (bypass_set) bypass_valid_q <= 1'b1;
    end

    always_comb bypass_load = bypass_set & ~bypass_clear & ~bypass_valid_q;

    if (DataRegNoReset) begin : gen_non_rst_byp_regs
      // DFFL: D-Flip-Flop, load enable
      always_ff @(posedge i_clk) begin
        if (bypass_load) bypass_data_q <= i_data;
      end
    end else begin : gen_rst_byp_regs
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) bypass_data_q <= data_t'(0);
        else if (bypass_load) bypass_data_q <= i_data;
      end
    end

    //////////////////////////////////////
    // Pipeline Register, Control SR FF //
    //////////////////////////////////////
    always_comb pipeline_set = internal_valid;
    always_comb pipeline_clear = i_ready;

`ifndef NO_SYNOPSYS_FF
  /* synopsys sync_set_reset "i_flush" */
`endif
    // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) pipeline_valid_q <= 1'b0;
      else if (i_flush) pipeline_valid_q <= 1'b0;
      else if (pipeline_set) pipeline_valid_q <= 1'b1;
      else if (pipeline_clear) pipeline_valid_q <= 1'b0;
    end

    always_comb pipeline_data_d = bypass_valid_q ? bypass_data_q : i_data;
    always_comb pipeline_load = internal_valid & internal_ready;

    if (DataRegNoReset) begin : gen_non_rst_pip_regs
      // DFFL: D-Flip-Flop, load enable
      always_ff @(posedge i_clk) begin
        if (pipeline_load) pipeline_data_q <= pipeline_data_d;
      end
    end else begin : gen_rst_pip_regs
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) pipeline_data_q <= data_t'(0);
        else if (pipeline_load) pipeline_data_q <= pipeline_data_d;
      end
    end

    ////////////////////////
    // Output assignments //
    ////////////////////////
    always_comb o_ready = ~bypass_valid_q;

    always_comb o_data = pipeline_data_q;
    always_comb o_valid = pipeline_valid_q;

  end : gen_spill_reg_back

  // TODO(@wolfgang.roenninger): Put this into a bind?
`ifndef SYNTHESIS
  flush_valid :
  assert property (@(posedge i_clk) disable iff (~i_rst_n) (i_flush |-> ~i_valid))
  else $warning("Trying to flush and feed the spill register simultaneously. You will lose data!");
`endif

endmodule
