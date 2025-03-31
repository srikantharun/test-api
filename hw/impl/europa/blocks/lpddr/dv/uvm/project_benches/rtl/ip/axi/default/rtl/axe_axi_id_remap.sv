// Copyright (c) 2014-2020 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// Remap AXI IDs from wide IDs at the subordinate port to narrower IDs at the manager port.
///
/// This module is designed to remap an overly wide, sparsely used ID space to a narrower, densely
/// used ID space.  This scenario occurs, for example, when an AXI manager has wide ID ports but
/// effectively only uses a (not necessarily contiguous) subset of IDs.
///
/// This module retains the independence of IDs.  That is, if two transactions have different IDs at
/// the subordinate port of this module, they are guaranteed to have different IDs at the manager port of
/// this module.  This implies a lower bound on the [width of IDs on the manager
/// port](#parameter.ManAxiIdWidth).  If you require narrower manager port IDs and can forgo ID
/// independence, use [`axi_id_serialize`](module.axi_id_serialize) instead.
///
/// Internally, a [table is used for remapping IDs](module.axi_id_remap_table).
module axe_axi_id_remap #(
  /// ID width of the AXI4+ATOP subordinate port.
  parameter int unsigned SubAxiIdWidth = axe_axi_default_types_pkg::WIDTH_ID_5,
  /// Maximum number of different IDs that can be in flight at the subordinate port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  ///
  /// The maximum value of this parameter is `2**SubAxiIdWidth`.
  parameter int unsigned SubMaxUniqIds = 32'd8,
  /// Maximum number of in-flight transactions with the same ID.
  ///
  /// It is legal for upstream to have more transactions than the maximum given by this parameter in
  /// flight for any ID, but a transaction exceeding the maximum will be stalled until another
  /// transaction with the same ID completes.
  parameter int unsigned MaxTxnsPerId  = 32'd8,
  /// ID width of the AXI4+ATOP manager port.
  ///
  /// The minimum value of this parameter is the ceiled binary logarithm of `SubMaxUniqIds`,
  /// because IDs at the manager port must be wide enough to represent IDs up to
  /// `SubMaxUniqIds-1`.
  ///
  /// If manager IDs are wider than the minimum, they are extended by prepending zeros.
  parameter int unsigned ManAxiIdWidth = axe_axi_default_types_pkg::WIDTH_ID_4,

  parameter type         axi_s_aw_t    = axe_axi_default_types_pkg::axi_aw_5_40_4_t,
  parameter type         axi_s_w_t     = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type         axi_s_b_t     = axe_axi_default_types_pkg::axi_b_5_4_t,
  parameter type         axi_s_ar_t    = axe_axi_default_types_pkg::axi_ar_5_40_4_t,
  parameter type         axi_s_r_t     = axe_axi_default_types_pkg::axi_r_5_64_4_t,
  parameter type         axi_m_aw_t    = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type         axi_m_w_t     = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type         axi_m_b_t     = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type         axi_m_ar_t    = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type         axi_m_r_t     = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  /// Rising-edge clock of all ports
  input  logic      i_clk,
  /// Asynchronous reset, active low
  input  logic      i_rst_n,

  // Subordinate port
  input  axi_s_aw_t i_axi_s_aw,
  input  logic      i_axi_s_aw_valid,
  output logic      o_axi_s_aw_ready,
  input  axi_s_w_t  i_axi_s_w,
  input  logic      i_axi_s_w_valid,
  output logic      o_axi_s_w_ready,
  output axi_s_b_t  o_axi_s_b,
  output logic      o_axi_s_b_valid,
  input  logic      i_axi_s_b_ready,
  input  axi_s_ar_t i_axi_s_ar,
  input  logic      i_axi_s_ar_valid,
  output logic      o_axi_s_ar_ready,
  output axi_s_r_t  o_axi_s_r,
  output logic      o_axi_s_r_valid,
  input  logic      i_axi_s_r_ready,

  // Manager port
  output axi_m_aw_t o_axi_m_aw,
  output logic      o_axi_m_aw_valid,
  input  logic      i_axi_m_aw_ready,
  output axi_m_w_t  o_axi_m_w,
  output logic      o_axi_m_w_valid,
  input  logic      i_axi_m_w_ready,
  input  axi_m_b_t  i_axi_m_b,
  input  logic      i_axi_m_b_valid,
  output logic      o_axi_m_b_ready,
  output axi_m_ar_t o_axi_m_ar,
  output logic      o_axi_m_ar_valid,
  input  logic      i_axi_m_ar_ready,
  input  axi_m_r_t  i_axi_m_r,
  input  logic      i_axi_m_r_valid,
  output logic      o_axi_m_r_ready
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  localparam int unsigned IdxWidth = cc_math_pkg::index_width(SubMaxUniqIds);


  if (SubAxiIdWidth == 0)                $fatal(1, "Parameter SubAxiIdWidth has to be larger than 0!");
  if (ManAxiIdWidth <  IdxWidth)         $fatal(1, "Parameter ManAxiIdWidth has to be at least IdxWidth!");
  if (SubMaxUniqIds == 0)                $fatal(1, "Parameter SubMaxUniqIds has to be larger than 0!");
  if (SubMaxUniqIds >  2**SubAxiIdWidth) $fatal(1, "Parameter SubMaxUniqIds may be at most 2**SubAxiIdWidth!");
  if (MaxTxnsPerId  == 0)                $fatal(1, "Parameter MaxTxnsPerId has to be larger than 0!");

  if ($bits(i_axi_s_aw.addr) != $bits(o_axi_m_aw.addr)) $fatal(1, "AXI AW address widths are not equal between ports!");
  if ($bits(i_axi_s_w.data)  != $bits(o_axi_m_w.data))  $fatal(1, "AXI W data widths are not equal between ports!");
  if ($bits(i_axi_s_ar.addr) != $bits(o_axi_m_ar.addr)) $fatal(1, "AXI AR address widths are not equal between ports!");
  if ($bits(o_axi_s_r.data)  != $bits(i_axi_m_r.data))  $fatal(1, "AXI R data widths are not equal between ports!");

  if ($bits(i_axi_s_aw.id) != SubAxiIdWidth) $fatal(1, "ID field of Subordinate AW struct does not match parameter 'SubAxiIdWidth'");
  if ($bits(o_axi_s_b.id)  != SubAxiIdWidth) $fatal(1, "ID field of Subordinate  B struct does not match parameter 'SubAxiIdWidth'");
  if ($bits(i_axi_s_ar.id) != SubAxiIdWidth) $fatal(1, "ID field of Subordinate AR struct does not match parameter 'SubAxiIdWidth'");
  if ($bits(o_axi_s_r.id)  != SubAxiIdWidth) $fatal(1, "ID field of Subordinate  R struct does not match parameter 'SubAxiIdWidth'");

  if ($bits(o_axi_m_aw.id) != ManAxiIdWidth) $fatal(1, "ID field of Manager AW struct does not match parameter 'ManAxiIdWidth'");
  if ($bits(i_axi_m_b.id)  != ManAxiIdWidth) $fatal(1, "ID field of Manager  B struct does not match parameter 'ManAxiIdWidth'");
  if ($bits(o_axi_m_ar.id) != ManAxiIdWidth) $fatal(1, "ID field of Manager AR struct does not match parameter 'ManAxiIdWidth'");
  if ($bits(i_axi_m_r.id)  != ManAxiIdWidth) $fatal(1, "ID field of Manager  R struct does not match parameter 'ManAxiIdWidth'");

  typedef logic [ManAxiIdWidth-1:0] axi_m_id_t;

  //////////////////////////////////////////////////////////////////////////////////////
  // Feed all signals that are not ID'd structs or flow control of AW and AR through. //
  //////////////////////////////////////////////////////////////////////////////////////
  always_comb o_axi_m_w       = i_axi_s_w;
  always_comb o_axi_m_w_valid = i_axi_s_w_valid;
  always_comb o_axi_s_w_ready = i_axi_m_w_ready;

  always_comb o_axi_s_b_valid = i_axi_m_b_valid;
  always_comb o_axi_m_b_ready = i_axi_s_b_ready;

  always_comb o_axi_s_r_valid = i_axi_m_r_valid;
  always_comb o_axi_m_r_ready = i_axi_s_r_ready;

  /////////////////////////////////////////////////////////////////////////////////
  // Remap tables keep track of in-flight bursts and their input and output IDs. //
  /////////////////////////////////////////////////////////////////////////////////
  typedef logic [SubMaxUniqIds-1:0]  field_t;
  typedef logic [SubAxiIdWidth-1:0]  axi_s_id_t;
  typedef logic [IdxWidth-1:0]       idx_t;
  field_t    wr_free,          rd_free,          both_free;
  axi_s_id_t                   rd_push_inp_id;
  idx_t      wr_free_oup_id,   rd_free_oup_id,   both_free_oup_id,
             wr_push_oup_id,   rd_push_oup_id,
             wr_exists_id,     rd_exists_id;
  logic      wr_exists,        rd_exists,
             wr_exists_full,   rd_exists_full,
             wr_full,          rd_full,
             wr_push,          rd_push,
             wr_pop,           rd_pop;

  ///////////////////////
  // Write remap table //
  ///////////////////////
  axi_s_id_t axi_s_b_id;

  axe_axi_id_remap_table #(
    .InpIdWidth   (SubAxiIdWidth),
    .MaxUniqInpIds(SubMaxUniqIds),
    .MaxTxnsPerId (MaxTxnsPerId)
  ) u_wr_table (
    .i_clk,
    .i_rst_n,
    .o_free         (wr_free),
    .o_free_oup_id  (wr_free_oup_id),
    .o_full         (wr_full),
    .i_push         (wr_push),
    .i_push_inp_id  (i_axi_s_aw.id),
    .i_push_oup_id  (wr_push_oup_id),
    .i_exists_inp_id(i_axi_s_aw.id),
    .o_exists       (wr_exists),
    .o_exists_oup_id(wr_exists_id),
    .o_exists_full  (wr_exists_full),
    .i_pop          (wr_pop),
    .i_pop_oup_id   (idx_t'(i_axi_m_b.id)),
    .o_pop_inp_id   (axi_s_b_id)
  );
  always_comb begin
    o_axi_m_aw    = i_axi_s_aw;
    o_axi_m_aw.id = axi_m_id_t'(wr_push_oup_id);
  end

  always_comb begin
    o_axi_s_b    = i_axi_m_b;
    o_axi_s_b.id = axi_s_id_t'(axi_s_b_id);
  end
  always_comb wr_pop = o_axi_s_b_valid & i_axi_s_b_ready;

  //////////////////////
  // Read remap table //
  //////////////////////
  axi_s_id_t axi_s_r_id;

  axe_axi_id_remap_table #(
    .InpIdWidth   (SubAxiIdWidth),
    .MaxUniqInpIds(SubMaxUniqIds),
    .MaxTxnsPerId (MaxTxnsPerId)
  ) u_rd_table (
    .i_clk,
    .i_rst_n,
    .o_free         (rd_free),
    .o_free_oup_id  (rd_free_oup_id),
    .o_full         (rd_full),
    .i_push         (rd_push),
    .i_push_inp_id  (rd_push_inp_id),
    .i_push_oup_id  (rd_push_oup_id),
    .i_exists_inp_id(i_axi_s_ar.id),
    .o_exists       (rd_exists),
    .o_exists_oup_id(rd_exists_id),
    .o_exists_full  (rd_exists_full),
    .i_pop          (rd_pop),
    .i_pop_oup_id   (idx_t'(i_axi_m_r.id)),
    .o_pop_inp_id   (axi_s_r_id)
  );

  always_comb begin
    o_axi_m_ar    = i_axi_s_ar;
    o_axi_m_ar.id = axi_m_id_t'(rd_push_oup_id);
  end

  always_comb begin
    o_axi_s_r    = i_axi_m_r;
    o_axi_s_r.id = axi_s_id_t'(axi_s_r_id);
  end
  always_comb rd_pop = o_axi_s_r_valid & i_axi_s_r_ready & o_axi_s_r.last;

  ///////////////////
  // Remap control //
  ///////////////////
  always_comb both_free = wr_free & rd_free;
  lzc #(
    .WIDTH(SubMaxUniqIds),
    .MODE (1'b0)
  ) u_lzc (
    .in_i   (both_free),
    .cnt_o  (both_free_oup_id),
    .empty_o(/*open*/)
  );

  // Handle requests.
  typedef enum logic [1:0] {
    Ready, HoldAR, HoldAW, HoldAx
  } state_e;

  idx_t   ar_id_d,   ar_id_q,
          aw_id_d,   aw_id_q;
  logic   ar_prio_d, ar_prio_q;
  state_e state_d,   state_q;
  always_comb begin
    o_axi_m_aw_valid = 1'b0;
    o_axi_s_aw_ready = 1'b0;

    wr_push          = 1'b0;
    wr_push_oup_id   =   '0;

    o_axi_m_ar_valid = 1'b0;
    o_axi_s_ar_ready = 1'b0;
    rd_push          = 1'b0;
    rd_push_inp_id   =   '0;
    rd_push_oup_id   =   '0;

    ar_id_d          = ar_id_q;
    aw_id_d          = aw_id_q;
    ar_prio_d        = ar_prio_q;
    state_d          = state_q;

    unique case (state_q)
      Ready: begin
        // Reads
        if (i_axi_s_ar_valid) begin
          // If a burst with the same input ID is already in flight or there are free output IDs:
          if ((rd_exists && !rd_exists_full) || (!rd_exists && !rd_full)) begin
            // Determine the output ID: if another in-flight burst had the same input ID, we must
            // reuse its output ID to maintain ordering; else, we assign the next free ID.
            rd_push_inp_id   = i_axi_s_ar.id;
            rd_push_oup_id   = rd_exists ? rd_exists_id : rd_free_oup_id;
            // Forward the AR and push a new entry to the read table.
            o_axi_m_ar_valid = 1'b1;
            rd_push          = 1'b1;
          end
        end

        // Writes
        if (i_axi_s_aw_valid) begin
          // If this is not an ATOP that gives rise to an R response, we can handle it in isolation
          // on the write direction.
          if (!i_axi_s_aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX]) begin
            // If a burst with the same input ID is already in flight or there are free output IDs:
            if ((wr_exists && !wr_exists_full) || (!wr_exists && !wr_full)) begin
              // Determine the output ID: if another in-flight burst had the same input ID, we must
              // reuse its output ID to maintain ordering; else, we assign the next free ID.
              wr_push_oup_id   = wr_exists ? wr_exists_id : wr_free_oup_id;
              // Forward the AW and push a new entry to the write table.
              o_axi_m_aw_valid = 1'b1;
              wr_push          = 1'b1;
            end
          // If this is an ATOP that gives rise to an R response, we must remap to an ID that is
          // free on both read and write direction and push also to the read table.
          // Only allowed if AR does not have arbitration priority
          end else if (!(ar_prio_q && o_axi_m_ar_valid)) begin
            // Nullify a potential AR at our output.  This is legal in this state.
            o_axi_m_ar_valid = 1'b0;
            o_axi_s_ar_ready = 1'b0;
            rd_push          = 1'b0;
            if ((|both_free)) begin
              // Use an output ID that is free in both directions.
              wr_push_oup_id = both_free_oup_id;
              rd_push_inp_id = i_axi_s_aw.id;
              rd_push_oup_id = both_free_oup_id;
              // Forward the AW and push a new entry to both tables.
              o_axi_m_aw_valid = 1'b1;
              rd_push          = 1'b1;
              wr_push          = 1'b1;
              // Give AR priority in the next cycle (so ATOPs cannot infinitely preempt ARs).
              ar_prio_d = 1'b1;
            end
          end
        end

        // Hold AR, AW, or both if they are valid but not yet ready.
        if (o_axi_m_ar_valid) begin
          o_axi_s_ar_ready = i_axi_m_ar_ready;
          if (!i_axi_m_ar_ready) begin
            ar_id_d = rd_push_oup_id;
          end
        end
        if (o_axi_m_aw_valid) begin
          o_axi_s_aw_ready = i_axi_m_aw_ready;
          if (!i_axi_m_aw_ready) begin
            aw_id_d = wr_push_oup_id;
          end
        end
        if ({o_axi_m_ar_valid, i_axi_m_ar_ready, o_axi_m_aw_valid, i_axi_m_aw_ready} == 4'b1010)
                                                                state_d = HoldAx;
        else if ({o_axi_m_ar_valid, i_axi_m_ar_ready} == 2'b10) state_d = HoldAR;
        else if ({o_axi_m_aw_valid, i_axi_m_aw_ready} == 2'b10) state_d = HoldAW;
        else                                                    state_d = Ready;

        if (o_axi_m_ar_valid && i_axi_m_ar_ready) begin
          ar_prio_d = 1'b0; // Reset AR priority, because handshake was successful in this cycle.
        end
      end

      HoldAR: begin
        // Drive `o_axi_m_ar.id` through `rd_push_oup_id`.
        rd_push_oup_id   = ar_id_q;
        o_axi_m_ar_valid = 1'b1;
        o_axi_s_ar_ready = i_axi_m_ar_ready;
        if (i_axi_m_ar_ready) begin
          state_d = Ready;
          ar_prio_d = 1'b0; // Reset AR priority, because handshake was successful in this cycle.
        end
      end

      HoldAW: begin
        // Drive o_axi_m_aw.id through `wr_push_oup_id`.
        wr_push_oup_id   = aw_id_q;
        o_axi_m_aw_valid = 1'b1;
        o_axi_s_aw_ready = i_axi_m_aw_ready;
        if (i_axi_m_aw_ready) begin
          state_d = Ready;
        end
      end

      HoldAx: begin
        rd_push_oup_id   = ar_id_q;
        o_axi_m_ar_valid = 1'b1;
        o_axi_s_ar_ready = i_axi_m_ar_ready;
        wr_push_oup_id   = aw_id_q;
        o_axi_m_aw_valid = 1'b1;
        o_axi_s_aw_ready = i_axi_m_aw_ready;
        unique case ({i_axi_m_ar_ready, i_axi_m_aw_ready})
          2'b01:   state_d = HoldAR;
          2'b10:   state_d = HoldAW;
          2'b11:   state_d = Ready;
          default: /*do nothing / stay in this state*/;
        endcase
        if (i_axi_m_ar_ready) begin
          ar_prio_d = 1'b0; // Reset AR priority, because handshake was successful in this cycle.
        end
      end

      default: state_d = Ready;
    endcase
  end

  ///////////////
  // Registers //
  ///////////////
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      ar_id_q   <= idx_t'(0);
      ar_prio_q <= 1'b0;
      aw_id_q   <= idx_t'(0);
      state_q   <= Ready;
    end else begin
      ar_id_q   <= ar_id_d;
      ar_prio_q <= ar_prio_d;
      aw_id_q   <= aw_id_d;
      state_q   <= state_d;
    end
  end

  // TODO(@wolfgang.roennigner): Move these to a bind
  `ifndef SYNTHESIS
  default disable iff (!i_rst_n);
  assert property (@(posedge i_clk) i_axi_s_aw_valid && o_axi_s_aw_ready
      |-> o_axi_m_aw_valid && i_axi_m_aw_ready);
  assert property (@(posedge i_clk) i_axi_m_b_valid && o_axi_m_b_ready
      |-> o_axi_s_b_valid && i_axi_s_b_ready);
  assert property (@(posedge i_clk) i_axi_s_ar_valid && o_axi_s_ar_ready
      |-> o_axi_m_ar_valid && i_axi_m_ar_ready);
  assert property (@(posedge i_clk) i_axi_m_r_valid && o_axi_m_r_ready
      |-> o_axi_s_r_valid && i_axi_s_r_ready);
  assert property (@(posedge i_clk) o_axi_s_r_valid
      |-> o_axi_s_r.last == i_axi_m_r.last);
  assert property (@(posedge i_clk) o_axi_m_ar_valid && !i_axi_m_ar_ready
      |=> o_axi_m_ar_valid && $stable(o_axi_m_ar.id));
  assert property (@(posedge i_clk) o_axi_m_aw_valid && !i_axi_m_aw_ready
      |=> o_axi_m_aw_valid && $stable(o_axi_m_aw.id));
  `endif
endmodule

/// Internal module of [`axi_id_remap`](module.axi_id_remap): Table to remap input to output IDs.
///
/// This module contains a table indexed by the output ID (type `idx_t`). Each table entry has two
/// fields: the input ID and a counter that records how many transactions with the input and output
/// ID of the entry are in-flight.
///
/// The mapping from input and output IDs is injective.  Therefore, when the table contains an entry
/// for an input ID with non-zero counter value, subsequent input IDs must use the same entry and
/// thus the same output ID.
///
/// ## Relation of types and table layout
/// ![diagram of table](axi_id_remap_table.svg)
///
/// ## Complexity
/// This module has:
/// - `MaxUniqInpIds * InpIdWidth * clog2(MaxTxnsPerId)` flip flops;
/// - `MaxUniqInpIds` comparators of width `InpIdWidth`;
/// - 2 leading-zero counters of width `MaxUniqInpIds`.
module axe_axi_id_remap_table #(
  /// Width of input IDs, therefore width of `id_inp_t`.
  parameter int unsigned  InpIdWidth    = 32'd0,
  /// Maximum number of different input IDs that can be in-flight. This defines the number of remap
  /// table entries.
  ///
  /// The maximum value of this parameter is `2**InpIdWidth`.
  parameter int unsigned  MaxUniqInpIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID.
  parameter int unsigned  MaxTxnsPerId  = 32'd0,
  /// Derived (**=do not override**) type of input IDs.
  localparam type         id_inp_t      = logic[InpIdWidth-1:0],
  /// Derived (**=do not override**) width of table index (ceiled binary logarithm of
  /// `MaxUniqInpIds`).
  localparam int unsigned IdxWidth      = cc_math_pkg::index_width(MaxUniqInpIds),
  /// Derived (**=do not override**) type of table index (width = `IdxWidth`).
  localparam type         idx_t         = logic[IdxWidth-1:0],
  /// Derived (**=do not override**) type with one bit per table entry (thus also output ID).
  localparam type         field_t       = logic[MaxUniqInpIds-1:0]
)(
  /// Rising-edge clock of all ports
  input  wire     i_clk,
  /// Asynchronous reset, active low
  input  wire     i_rst_n,

  /// One bit per table entry / output ID that indicates whether the entry is free.
  output field_t  o_free,
  /// Lowest free output ID.  Only valid if the table is not full (i.e., `!o_full`).
  output idx_t    o_free_oup_id,
  /// Indicates whether the table is full.
  output logic    o_full,

  /// Push an input/output ID pair to the table.
  input  logic    i_push,
  /// Input ID to be pushed. If the table already contains this ID, its counter must be smaller than
  /// `MaxTxnsPerId`.
  input  id_inp_t i_push_inp_id,
  /// Output ID to be pushed.  If the table already contains the input ID to be pushed, the output
  /// ID **must** match the output ID of the existing entry with the same input ID.
  input  idx_t    i_push_oup_id,

  /// Input ID to look up in the table.
  input  id_inp_t i_exists_inp_id,
  /// Indicates whether the given input ID exists in the table.
  output logic    o_exists,
  /// The output ID of the given input ID.  Only valid if the input ID exists (i.e., `o_exists`).
  output idx_t    o_exists_oup_id,
  /// Indicates whether the maximum number of transactions for the given input ID is reached.  Only
  /// valid if the input ID exists (i.e., `o_exists`).
  output logic    o_exists_full,

  /// Pop an output ID from the table.  This reduces the counter for the table index given in
  /// `i_pop_oup_id` by one.
  input  logic    i_pop,
  /// Output ID to be popped.  The counter for this ID must be larger than `0`.
  input  idx_t    i_pop_oup_id,
  /// Input ID corresponding to the popped output ID.
  output id_inp_t o_pop_inp_id
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  if (InpIdWidth == 0)                   $fatal(1, "Parameter: 'InpIdWidth' has to be not 0;");
  if (MaxUniqInpIds == 0)                $fatal(1, "Parameter: 'MaxUniqInpIds' has to be not 0;");
  if (MaxUniqInpIds > (1 << InpIdWidth)) $fatal(1, "Parameter: 'MaxUniqInpIds' can not be represented by 'InpIdWidth';");
  if (MaxTxnsPerId == 0)                 $fatal(1, "Parameter: 'MaxTxnsPerId' has to be not 0;");
  if (IdxWidth     == 0)                 $fatal(1, "Localparam: 'IdxWidth' has to be not 0;");

  // Counter width, derived to hold numbers up to `MaxTxnsPerId`.
  localparam int unsigned CntWidth = $clog2(MaxTxnsPerId+1);
  // Counter that tracks the number of in-flight transactions with an ID.
  typedef logic [CntWidth-1:0] cnt_t;

  // Type of a table entry.
  typedef struct packed {
    id_inp_t  inp_id;
    cnt_t     cnt;
  } entry_t;

  // Table indexed by output IDs that contains the corresponding input IDs
  entry_t [MaxUniqInpIds-1:0] table_d, table_q;

  // Determine lowest free output ID.
  for (genvar i = 0; unsigned'(i) < MaxUniqInpIds; i++) begin : gen_o_free
    assign o_free[i] = table_q[i].cnt == '0;
  end
  lzc #(
    .WIDTH(MaxUniqInpIds),
    .MODE (1'b0)
  ) u_lzc_free (
    .in_i   (o_free),
    .cnt_o  (o_free_oup_id),
    .empty_o(o_full)
  );

  // Determine the input ID for a given output ID.
  if (MaxUniqInpIds == 1) begin : gen_pop_for_single_unique_inp_id
    assign o_pop_inp_id = table_q[0].inp_id;
  end else begin : gen_pop_for_multiple_unique_inp_ids
    assign o_pop_inp_id = table_q[i_pop_oup_id].inp_id;
  end

  // Determine if given output ID is already used and, if it is, by which input ID.
  field_t match;
  for (genvar i = 0; unsigned'(i) < MaxUniqInpIds; i++) begin : gen_match
    assign match[i] = (table_q[i].cnt > 0)
                    & (table_q[i].inp_id == i_exists_inp_id);
  end
  logic no_match;
  lzc #(
      .WIDTH(MaxUniqInpIds),
      .MODE (1'b0)
  ) u_lzc_match (
      .in_i   (match),
      .cnt_o  (o_exists_oup_id),
      .empty_o(no_match)
  );
  assign o_exists      = ~no_match;
  if (MaxUniqInpIds == 1) begin : gen_exists_full_for_single_unique_inp_id
    assign o_exists_full = table_q[0].cnt == MaxTxnsPerId;
  end else begin : gen_exists_full_for_multiple_unique_inp_ids
    assign o_exists_full = table_q[o_exists_oup_id].cnt == MaxTxnsPerId;
  end

  // Push and pop table entries.
  always_comb begin
    table_d = table_q;
    if (i_push) begin
      table_d[i_push_oup_id].inp_id  = i_push_inp_id;
      table_d[i_push_oup_id].cnt    += 1;
    end
    if (i_pop) begin
      table_d[i_pop_oup_id].cnt -= 1;
    end
  end

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)             table_q <= '0;
    else if (i_push || i_pop) table_q <= table_d;
  end

  // TODO(@wolfgang.roennigner): Move these into a bind
  // Assertions
  `ifndef SYNTHESIS
    default disable iff (!i_rst_n);
    assume property (@(posedge i_clk) i_push |->
        table_q[i_push_oup_id].cnt == '0 || table_q[i_push_oup_id].inp_id == i_push_inp_id)
      else $error("Push must be to empty output ID or match existing input ID!");
    assume property (@(posedge i_clk) i_push |-> table_q[i_push_oup_id].cnt < MaxTxnsPerId)
      else $error("Maximum number of in-flight bursts must not be exceeded!");
    assume property (@(posedge i_clk) i_pop |-> table_q[i_pop_oup_id].cnt > 0)
      else $error("Pop must target output ID with non-zero counter!");
    assume property (@(posedge i_clk) $onehot0(match))
      else $error("Input ID in table must be unique!");
  `endif

endmodule
