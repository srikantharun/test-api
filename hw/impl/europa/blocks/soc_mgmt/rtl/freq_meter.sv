// Copyright 2020 ETH Zurich
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Stefan Mach <smach@iis.ee.ethz.ch>
// Thomas Benz <tbenz@iis.ee.ethz.ch>
// Paul Scheffler <paulsc@iis.ee.ethz.ch>
// Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

//`include "common_cells/registers.svh"

/// A simple frequency meter.
///
/// Measures the integer frequency multiplication factor relative to a reference
/// clock.

module freq_meter #(
  /// Number of clocks to observe.
  parameter int NumClks = 1,
  /// Number of bits in the frequency counters.
  parameter int Width = 32,
  /// Number of synchronization stages for refclk sampling.
  parameter int SyncStages = 2
)(
  input  wire                           i_clk,
  input  wire                           i_rst_n,
  input  wire                           i_clk_ref,
  input  logic                          test_mode,
  input  wire  [NumClks-1:0]            i_obs_clk,
  output logic [NumClks-1:0][Width-1:0] o_obs_freq
);

  //============================================================================
  typedef logic [Width-1:0] count_t;

  count_t [NumClks-1:0] count_current_q;
  logic [NumClks-1:0] sample;

  // Generate the gray counters running on each of the observed clocks.
  for (genvar i = 0; i < NumClks; i++) begin : gen_obs
    logic clk_ref_now, clk_ref_last;
    logic obs_rst_n;

    axe_tcl_seq_sync #(
      .SyncStages ( SyncStages ),
      .ResetValue ( 0          ),
      .Ratio      ( 99         )
    ) u_reset_sync (
      .i_clk   ( i_obs_clk[i] ),
      .i_rst_n ( i_rst_n      ),
      .i_d     ( 1'h1         ),
      .o_q     ( obs_rst_n    )
    );

    axe_tcl_seq_sync #(
      .SyncStages ( SyncStages ),
      .ResetValue ( 0          ),
      .Ratio      ( 0          )
    ) u_cdc_level (
      .i_clk   ( i_obs_clk[i] ),
      .i_rst_n ( obs_rst_n    ),
      .i_d     ( i_clk_ref    ),
      .o_q     ( clk_ref_now  )
    );


    always_ff @ (posedge i_obs_clk[i] or negedge obs_rst_n) begin
      if (!obs_rst_n) begin
        clk_ref_last <= 1'h0;
      end else begin
       clk_ref_last <= clk_ref_now;
      end
    end


    assign sample[i] = ~clk_ref_last & clk_ref_now;

    always_ff @ (posedge i_obs_clk[i] or negedge obs_rst_n) begin
      if (!obs_rst_n) begin
        count_current_q[i] <= {NumClks{1'h0}};
      end else begin
        count_current_q[i] <= sample[i] ? {NumClks{1'h0}} : count_current_q[i] + {{NumClks-1{1'h0}}, 1'h1};
      end
    end


    // We use a simple CDC here to transport the sampled frequency across the
    // clock domain boundary. Note that we ignore the handshake back-pressure,
    // since the CDC ensures that new input data is sampled in the very clock
    // cycle the `valid_i` signal is asserted, and the output on the destination
    // side only ever changes to reflect a new valid datum.

    axe_ccl_cdc_bus #(
      .SyncStages(SyncStages),
      .data_t    (count_t)
    ) i_cdc_handshake (
      .i_src_clk    ( i_obs_clk[i]       ),
      .i_src_rst_n  ( obs_rst_n          ),
      .i_src_en     ( sample[i]          ),
      .i_src_data   ( count_current_q[i] ),
      .o_src_busy   (                    ), // ASO-UNUSED_OUTPUT : No backpressure.

      .i_dst_clk    ( i_clk              ),
      .i_dst_rst_n  ( i_rst_n            ),
      .o_dst_data   ( o_obs_freq[i]      ),
      .o_dst_update (                    ) // ASO-UNUSED_OUTPUT : No update signal needed.
    );

  end
endmodule
