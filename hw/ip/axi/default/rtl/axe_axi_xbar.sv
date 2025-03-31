// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// AXI4+ATOP crossbar with an arbitrary number of slave and master ports.
///
module axe_axi_xbar #(
  /// The number of subordinate ports
  parameter int unsigned                           NumSubPorts        = axe_axi_default_types_pkg::NUM_PORTS,
  /// The number of manager ports
  parameter int unsigned                           NumManPorts        = axe_axi_default_types_pkg::NUM_PORTS,
  /// The maximum number of outstanding transactions on each subordinate port per ID
  parameter int unsigned                           MaxSubTxn          = 8,
  /// The maximum number of outstanding write transactions on each manager port
  parameter int unsigned                           MaxManTxn          = 8,
  /// The Fifos in the design are configured in fall-through mode
  parameter int unsigned                           FallThrough        = 1'b0,
  /// The latency mode of the ports, inserts spill registers at the ports
  parameter axi_xbar_pkg::xbar_latency_e           LatencyMode        = axi_xbar_pkg::CUT_ALL_PORTS,
  /// The amount of pipeline stages in the middle of the cross, between the demux and muxes
  parameter int unsigned                           LatencyCross       = 0,
  /// Axi Id width of the subordinate ports, the submodules require that
  /// The ID width increses and is calculated by: `SubAxiIdWidth + $clog2(NumSubPorts)`
  /// See `axe_axi_mux`
  parameter int unsigned                           SubAxiIdWidth      = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Indicate that the incoming IDs are unique for each transaction, this causes the demux to be simpler
  parameter bit                                    UniqueIds          = 1'b0,

  /// The actual slice width of a transaction ID that determines the uniques of an ID.
  /// This directly translates to the amount of counters instanziated:
  /// `(2**AxiIdUsedWidth) * NumSubPorts`
  /// Note: This parameter might change in the future.
  parameter int unsigned                           AxiIdUsedWidth     = 3,
  /// The address with of the AXI structs
  parameter int unsigned                           AxiAddrWidth       = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// The number of address rules
  parameter int unsigned                           NumAddrRules       = 1,
  /// Support atomic operations from AXI5 (ATOPS)
  parameter bit                                    SupportAtops       = 1'b1,
  /// Define the connectivity between subordinates and manager ports
  parameter bit [NumSubPorts-1:0][NumManPorts-1:0] Connectivity       = '1,
  /// Address rule type for the address decoders from `common_cells:addr_decode`.
  /// Example types are provided in `axi_pkg`.
  /// Required struct fields:
  ///
  /// ```systemverilog
  /// typedef struct packed {
  ///   int m_select_t index;
  ///   axi_addr_t     addr_start;
  ///   axi_addr_t     addr_end;
  /// } addr_rule_t;
  /// ```
  parameter type                                   addr_rule_t        = axe_axi_default_types_pkg::xbar_rule_40_t,
  /// Subordinate AW channel type
  parameter type                                   axi_s_aw_t         = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  /// Manager AW channel type
  parameter type                                   axi_m_aw_t         = axe_axi_default_types_pkg::axi_aw_5_40_4_t,
  /// Subordinate *AND* Manager W channel type
  parameter type                                   axi_w_t            = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  /// Subordinate B channel type
  parameter type                                   axi_s_b_t          = axe_axi_default_types_pkg::axi_b_4_4_t,
  /// Manager B channel type
  parameter type                                   axi_m_b_t          = axe_axi_default_types_pkg::axi_b_5_4_t,
  /// Subordinate AR channel type
  parameter type                                   axi_s_ar_t         = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  /// Manager AR channel type
  parameter type                                   axi_m_ar_t         = axe_axi_default_types_pkg::axi_ar_5_40_4_t,
  /// Subordinate R channel type
  parameter type                                   axi_s_r_t          = axe_axi_default_types_pkg::axi_r_4_64_4_t,
  /// Manager R channel type
  parameter type                                   axi_m_r_t          = axe_axi_default_types_pkg::axi_r_5_64_4_t,

  /// Dependent parameter: The width of the default manager port selection
  localparam int unsigned                          ManPortSelectWidth = cc_math_pkg::index_width(NumManPorts),
  /// Dependent parameter: The type definition of the default port selection signal
  localparam type                                  m_select_t         = logic[ManPortSelectWidth-1:0]
)(
  /// Clock, positive edge triggered.
  input  wire i_clk,
  /// Asynchronous reset, active low.
  input  wire i_rst_n,

  // Subordinate Port
  input  axi_s_aw_t  i_axi_s_aw[NumSubPorts],
  input  logic       i_axi_s_aw_valid[NumSubPorts],
  output logic       o_axi_s_aw_ready[NumSubPorts],
  input  axi_w_t     i_axi_s_w[NumSubPorts],
  input  logic       i_axi_s_w_valid[NumSubPorts],
  output logic       o_axi_s_w_ready[NumSubPorts],
  output axi_s_b_t   o_axi_s_b[NumSubPorts],
  output logic       o_axi_s_b_valid[NumSubPorts],
  input  logic       i_axi_s_b_ready[NumSubPorts],
  input  axi_s_ar_t  i_axi_s_ar[NumSubPorts],
  input  logic       i_axi_s_ar_valid[NumSubPorts],
  output logic       o_axi_s_ar_ready[NumSubPorts],
  output axi_s_r_t   o_axi_s_r[NumSubPorts],
  output logic       o_axi_s_r_valid[NumSubPorts],
  input  logic       i_axi_s_r_ready[NumSubPorts],

  // Manager Port
  output axi_m_aw_t  o_axi_m_aw[NumManPorts],
  output logic       o_axi_m_aw_valid[NumManPorts],
  input  logic       i_axi_m_aw_ready[NumManPorts],
  output axi_w_t     o_axi_m_w[NumManPorts],
  output logic       o_axi_m_w_valid[NumManPorts],
  input  logic       i_axi_m_w_ready[NumManPorts],
  input  axi_m_b_t   i_axi_m_b[NumManPorts],
  input  logic       i_axi_m_b_valid[NumManPorts],
  output logic       o_axi_m_b_ready[NumManPorts],
  output axi_m_ar_t  o_axi_m_ar[NumManPorts],
  output logic       o_axi_m_ar_valid[NumManPorts],
  input  logic       i_axi_m_ar_ready[NumManPorts],
  input  axi_m_r_t   i_axi_m_r[NumManPorts],
  input  logic       i_axi_m_r_valid[NumManPorts],
  output logic       o_axi_m_r_ready[NumManPorts],

  /// The address map, replicated on all subordinate ports
  input  addr_rule_t i_addr_map[NumAddrRules],
  /// Enable default routing on decode errors
  input  logic       i_default_m_port_en[NumSubPorts],
  /// Default routing mapping per subordinate port
  input  m_select_t  i_default_m_port[NumSubPorts]
);

  //////////////////////////
  // Parameter sanitation //
  //////////////////////////
  // we want the log here as for one port it should not increase!
  localparam int unsigned ManAxiIdWidth = SubAxiIdWidth + unsigned'($clog2(NumSubPorts));

  if ($bits(i_axi_s_aw[0].id) != SubAxiIdWidth) $fatal(1, "Sub AW id width of type not equal parameter.");
  if ($bits(o_axi_s_b[0].id)  != SubAxiIdWidth) $fatal(1, "Sub  B id width of type not equal parameter.");
  if ($bits(i_axi_s_ar[0].id) != SubAxiIdWidth) $fatal(1, "Sub AR id width of type not equal parameter.");
  if ($bits(o_axi_s_r[0].id)  != SubAxiIdWidth) $fatal(1, "Sub  R id width of type not equal parameter.");

  if ($bits(o_axi_m_aw[0].id) != ManAxiIdWidth) $fatal(1, "Man AW id width of type not equal parameter.");
  if ($bits(i_axi_m_b[0].id)  != ManAxiIdWidth) $fatal(1, "Man  B id width of type not equal parameter.");
  if ($bits(o_axi_m_ar[0].id) != ManAxiIdWidth) $fatal(1, "Man AR id width of type not equal parameter.");
  if ($bits(i_axi_m_r[0].id)  != ManAxiIdWidth) $fatal(1, "Man  R id width of type not equal parameter.");

  if ($bits(i_axi_s_aw[0].addr) != AxiAddrWidth) $fatal(1, "Sub AW addr width of type not equal parameter.");
  if ($bits(i_axi_s_ar[0].addr) != AxiAddrWidth) $fatal(1, "Sub AR addr width of type not equal parameter.");

  if ($bits(o_axi_m_aw[0].addr) != AxiAddrWidth) $fatal(1, "Man AW addr width of type not equal parameter.");
  if ($bits(o_axi_m_ar[0].addr) != AxiAddrWidth) $fatal(1, "Man AR addr width of type not equal parameter.");

  // Address tpye for inidvidual address signals
  typedef logic [AxiAddrWidth-1:0] axi_addr_t;
  // to account for the decoding error subordinate
  typedef logic [cc_math_pkg::index_width(NumManPorts + 1)-1:0] man_port_idx_t;

  if ($bits(i_addr_map[0].addr_start) != AxiAddrWidth) $fatal(1, "Address map address wield does not match AxiAddrWidth. is: %d and %d",
      $bits(i_addr_map[0].addr_start),   AxiAddrWidth);
  if ($bits(i_addr_map[0].addr_end)   != AxiAddrWidth) $fatal(1, "Address map address wield does not match AxiAddrWidth. is: %d and %d",
      $bits(i_addr_map[0].addr_end),     AxiAddrWidth);

  // signals from the axi_demuxes, one index more for decode error
  axi_s_aw_t sub_aw[NumSubPorts][NumManPorts+1];
  logic      sub_aw_valid[NumSubPorts][NumManPorts+1];
  logic      sub_aw_ready[NumSubPorts][NumManPorts+1];
  axi_w_t    sub_w[NumSubPorts][NumManPorts+1];
  logic      sub_w_valid[NumSubPorts][NumManPorts+1];
  logic      sub_w_ready[NumSubPorts][NumManPorts+1];
  axi_s_b_t  sub_b[NumSubPorts][NumManPorts+1];
  logic      sub_b_valid[NumSubPorts][NumManPorts+1];
  logic      sub_b_ready[NumSubPorts][NumManPorts+1];
  axi_s_ar_t sub_ar[NumSubPorts][NumManPorts+1];
  logic      sub_ar_valid[NumSubPorts][NumManPorts+1];
  logic      sub_ar_ready[NumSubPorts][NumManPorts+1];
  axi_s_r_t  sub_r[NumSubPorts][NumManPorts+1];
  logic      sub_r_valid[NumSubPorts][NumManPorts+1];
  logic      sub_r_ready[NumSubPorts][NumManPorts+1];

  // signals into the axi_muxes, are of type slave as the multiplexer extends the ID
  axi_s_aw_t man_aw[NumManPorts][NumSubPorts];
  logic      man_aw_valid[NumManPorts][NumSubPorts];
  logic      man_aw_ready[NumManPorts][NumSubPorts];
  axi_w_t    man_w[NumManPorts][NumSubPorts];
  logic      man_w_valid[NumManPorts][NumSubPorts];
  logic      man_w_ready[NumManPorts][NumSubPorts];
  axi_s_b_t  man_b[NumManPorts][NumSubPorts];
  logic      man_b_valid[NumManPorts][NumSubPorts];
  logic      man_b_ready[NumManPorts][NumSubPorts];
  axi_s_ar_t man_ar[NumManPorts][NumSubPorts];
  logic      man_ar_valid[NumManPorts][NumSubPorts];
  logic      man_ar_ready[NumManPorts][NumSubPorts];
  axi_s_r_t  man_r[NumManPorts][NumSubPorts];
  logic      man_r_valid[NumManPorts][NumSubPorts];
  logic      man_r_ready[NumManPorts][NumSubPorts];

  for (genvar sub_port_idx = 0; sub_port_idx < NumSubPorts; sub_port_idx++) begin : gen_sub_demux
    m_select_t      dec_aw,        dec_ar;
    man_port_idx_t  slv_aw_select, slv_ar_select;
    logic           dec_aw_valid,  dec_aw_error;
    logic           dec_ar_valid,  dec_ar_error;

    cc_decode_addr #(
      .NumRules(NumAddrRules),
      .index_t (m_select_t),
      .addr_t  (axi_addr_t),
      .rule_t  (addr_rule_t)
    ) u_axi_aw_decode (
      .i_address         (i_axi_s_aw[sub_port_idx].addr),
      .i_address_map     (i_addr_map),
      .o_index           (dec_aw),
      .o_decode_valid    (dec_aw_valid),
      .o_decode_error    (dec_aw_error),
      .i_default_index_en(i_default_m_port_en[sub_port_idx]),
      .i_default_index   (i_default_m_port[sub_port_idx]),
      .i_config_ongoing  (1'b0)
    );

    cc_decode_addr #(
      .NumRules(NumAddrRules ),
      .index_t (m_select_t),
      .addr_t  (axi_addr_t),
      .rule_t  (addr_rule_t)
    ) u_axi_ar_decode (
      .i_address         (i_axi_s_ar[sub_port_idx].addr),
      .i_address_map     (i_addr_map),
      .o_index           (dec_ar),
      .o_decode_valid    (dec_ar_valid),
      .o_decode_error    (dec_ar_error),
      .i_default_index_en(i_default_m_port_en[sub_port_idx]),
      .i_default_index   (i_default_m_port[sub_port_idx]),
      .i_config_ongoing  (1'b0)
    );

    always_comb slv_aw_select = dec_aw_error ? man_port_idx_t'(NumManPorts) : man_port_idx_t'(dec_aw);
    always_comb slv_ar_select = dec_ar_error ? man_port_idx_t'(NumManPorts) : man_port_idx_t'(dec_ar);

    ////////////////
    // Assertions //
    ////////////////
    `ifndef SYNTHESIS
    `ifdef ASSERTIONS_ON

    // make sure that the default slave does not get changed, if there is an unserved Ax
    default disable iff (~i_rst_n);
    default_aw_mst_port_en: assert property(
      @(posedge i_clk) (i_axi_s_aw_valid[sub_port_idx] && !o_axi_s_aw_ready[sub_port_idx])
          |=> $stable(i_default_m_port_en[sub_port_idx]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port enable, when there is an unserved Aw beat. Slave Port: %0d", sub_port_idx));
    default_aw_mst_port: assert property(
      @(posedge i_clk) (i_axi_s_aw_valid[sub_port_idx] && !o_axi_s_aw_ready[sub_port_idx])
          |=> $stable(i_default_m_port[sub_port_idx]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port when there is an unserved Aw beat. Slave Port: %0d", sub_port_idx));
    default_ar_mst_port_en: assert property(
      @(posedge i_clk) (i_axi_s_ar_valid[sub_port_idx] && !o_axi_s_ar_ready[sub_port_idx])
          |=> $stable(i_default_m_port_en[sub_port_idx]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when there is an unserved Ar beat. Slave Port: %0d", sub_port_idx));
    default_ar_mst_port: assert property(
      @(posedge i_clk) (i_axi_s_ar_valid[sub_port_idx] && !o_axi_s_ar_ready[sub_port_idx])
          |=> $stable(i_default_m_port[sub_port_idx]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port when there is an unserved Ar beat. Slave Port: %0d", sub_port_idx));
    `endif
    `endif

    axe_axi_demux #(
      .NumPorts    (NumManPorts + 1),
      .AxiIdWidth  (SubAxiIdWidth),
      .MaxTxn      (MaxSubTxn),
      .AxiLookBits (AxiIdUsedWidth),
      .SupportAtops(SupportAtops),
      .UniqueIds   (UniqueIds),
      .CutAw       (LatencyMode[9]),
      .CutW        (LatencyMode[8]),
      .CutB        (LatencyMode[7]),
      .CutAr       (LatencyMode[6]),
      .CutR        (LatencyMode[5]),
      .axi_aw_t    (axi_s_aw_t),
      .axi_w_t     (axi_w_t),
      .axi_b_t     (axi_s_b_t),
      .axi_ar_t    (axi_s_ar_t),
      .axi_r_t     (axi_s_r_t)
    ) u_axi_demux (
      .i_clk,
      .i_rst_n,

      .i_axi_s_aw       (i_axi_s_aw[sub_port_idx]),
      .i_axi_s_aw_select(slv_aw_select),
      .i_axi_s_aw_valid (i_axi_s_aw_valid[sub_port_idx]),
      .o_axi_s_aw_ready (o_axi_s_aw_ready[sub_port_idx]),
      .i_axi_s_w        (i_axi_s_w[sub_port_idx]),
      .i_axi_s_w_valid  (i_axi_s_w_valid[sub_port_idx]),
      .o_axi_s_w_ready  (o_axi_s_w_ready[sub_port_idx]),
      .o_axi_s_b        (o_axi_s_b[sub_port_idx]),
      .o_axi_s_b_valid  (o_axi_s_b_valid[sub_port_idx]),
      .i_axi_s_b_ready  (i_axi_s_b_ready[sub_port_idx]),
      .i_axi_s_ar       (i_axi_s_ar[sub_port_idx]),
      .i_axi_s_ar_select(slv_ar_select),
      .i_axi_s_ar_valid (i_axi_s_ar_valid[sub_port_idx]),
      .o_axi_s_ar_ready (o_axi_s_ar_ready[sub_port_idx]),
      .o_axi_s_r        (o_axi_s_r[sub_port_idx]),
      .o_axi_s_r_valid  (o_axi_s_r_valid[sub_port_idx]),
      .i_axi_s_r_ready  (i_axi_s_r_ready[sub_port_idx]),

      .o_axi_m_aw       (sub_aw[sub_port_idx]),
      .o_axi_m_aw_valid (sub_aw_valid[sub_port_idx]),
      .i_axi_m_aw_ready (sub_aw_ready[sub_port_idx]),
      .o_axi_m_w        (sub_w[sub_port_idx]),
      .o_axi_m_w_valid  (sub_w_valid[sub_port_idx]),
      .i_axi_m_w_ready  (sub_w_ready[sub_port_idx]),
      .i_axi_m_b        (sub_b[sub_port_idx]),
      .i_axi_m_b_valid  (sub_b_valid[sub_port_idx]),
      .o_axi_m_b_ready  (sub_b_ready[sub_port_idx]),
      .o_axi_m_ar       (sub_ar[sub_port_idx]),
      .o_axi_m_ar_valid (sub_ar_valid[sub_port_idx]),
      .i_axi_m_ar_ready (sub_ar_ready[sub_port_idx]),
      .i_axi_m_r        (sub_r[sub_port_idx]),
      .i_axi_m_r_valid  (sub_r_valid[sub_port_idx]),
      .o_axi_m_r_ready  (sub_r_ready[sub_port_idx])
    );

    localparam logic [39:0] RespErrorData = {32'hBAD_CAB1E, sub_port_idx[0+:8]};

    axe_axi_err_sub #(
      .AxiIdWidth  (SubAxiIdWidth),
      .Resp        (axi_pkg::RespDecErr),
      .ReadData    (RespErrorData),
      .MaxTxn      (4), // Minimize ressource consumption
      .SupportAtops(SupportAtops),
      .axi_aw_t    (axi_s_aw_t),
      .axi_w_t     (axi_w_t),
      .axi_b_t     (axi_s_b_t),
      .axi_ar_t    (axi_s_ar_t),
      .axi_r_t     (axi_s_r_t)
    ) u_axe_axi_err_sub (
      .i_clk,
      .i_rst_n,

      .i_axi_s_aw      (sub_aw[sub_port_idx][NumManPorts]),
      .i_axi_s_aw_valid(sub_aw_valid[sub_port_idx][NumManPorts]),
      .o_axi_s_aw_ready(sub_aw_ready[sub_port_idx][NumManPorts]),
      .i_axi_s_w       (sub_w[sub_port_idx][NumManPorts]),
      .i_axi_s_w_valid (sub_w_valid[sub_port_idx][NumManPorts]),
      .o_axi_s_w_ready (sub_w_ready[sub_port_idx][NumManPorts]),
      .o_axi_s_b       (sub_b[sub_port_idx][NumManPorts]),
      .o_axi_s_b_valid (sub_b_valid[sub_port_idx][NumManPorts]),
      .i_axi_s_b_ready (sub_b_ready[sub_port_idx][NumManPorts]),
      .i_axi_s_ar      (sub_ar[sub_port_idx][NumManPorts]),
      .i_axi_s_ar_valid(sub_ar_valid[sub_port_idx][NumManPorts]),
      .o_axi_s_ar_ready(sub_ar_ready[sub_port_idx][NumManPorts]),
      .o_axi_s_r       (sub_r[sub_port_idx][NumManPorts]),
      .o_axi_s_r_valid (sub_r_valid[sub_port_idx][NumManPorts]),
      .i_axi_s_r_ready (sub_r_ready[sub_port_idx][NumManPorts])
    );
  end

  // cross all channels
  for (genvar sub_port_idx = 0; unsigned'(sub_port_idx) < NumSubPorts; sub_port_idx++) begin : gen_sub_cross
    for (genvar man_port_idx = 0; unsigned'(man_port_idx) < NumManPorts; man_port_idx++) begin : gen_man_cross
      if (Connectivity[sub_port_idx][man_port_idx]) begin : gen_con
        axe_axi_multicut #(
          .NumCuts (LatencyCross),
          .axi_aw_t(axi_s_aw_t),
          .axi_w_t (axi_w_t),
          .axi_b_t (axi_s_b_t),
          .axi_ar_t(axi_s_ar_t),
          .axi_r_t (axi_s_r_t)
        ) u_axi_multicut_xbar_pipeline (
          .i_clk,
          .i_rst_n,

          .i_axi_s_aw      (sub_aw[sub_port_idx][man_port_idx]),
          .i_axi_s_aw_valid(sub_aw_valid[sub_port_idx][man_port_idx]),
          .o_axi_s_aw_ready(sub_aw_ready[sub_port_idx][man_port_idx]),
          .i_axi_s_w       (sub_w[sub_port_idx][man_port_idx]),
          .i_axi_s_w_valid (sub_w_valid[sub_port_idx][man_port_idx]),
          .o_axi_s_w_ready (sub_w_ready[sub_port_idx][man_port_idx]),
          .o_axi_s_b       (sub_b[sub_port_idx][man_port_idx]),
          .o_axi_s_b_valid (sub_b_valid[sub_port_idx][man_port_idx]),
          .i_axi_s_b_ready (sub_b_ready[sub_port_idx][man_port_idx]),
          .i_axi_s_ar      (sub_ar[sub_port_idx][man_port_idx]),
          .i_axi_s_ar_valid(sub_ar_valid[sub_port_idx][man_port_idx]),
          .o_axi_s_ar_ready(sub_ar_ready[sub_port_idx][man_port_idx]),
          .o_axi_s_r       (sub_r[sub_port_idx][man_port_idx]),
          .o_axi_s_r_valid (sub_r_valid[sub_port_idx][man_port_idx]),
          .i_axi_s_r_ready (sub_r_ready[sub_port_idx][man_port_idx]),

          .o_axi_m_aw      (man_aw[man_port_idx][sub_port_idx]),
          .o_axi_m_aw_valid(man_aw_valid[man_port_idx][sub_port_idx]),
          .i_axi_m_aw_ready(man_aw_ready[man_port_idx][sub_port_idx]),
          .o_axi_m_w       (man_w[man_port_idx][sub_port_idx]),
          .o_axi_m_w_valid (man_w_valid[man_port_idx][sub_port_idx]),
          .i_axi_m_w_ready (man_w_ready[man_port_idx][sub_port_idx]),
          .i_axi_m_b       (man_b[man_port_idx][sub_port_idx]),
          .i_axi_m_b_valid (man_b_valid[man_port_idx][sub_port_idx]),
          .o_axi_m_b_ready (man_b_ready[man_port_idx][sub_port_idx]),
          .o_axi_m_ar      (man_ar[man_port_idx][sub_port_idx]),
          .o_axi_m_ar_valid(man_ar_valid[man_port_idx][sub_port_idx]),
          .i_axi_m_ar_ready(man_ar_ready[man_port_idx][sub_port_idx]),
          .i_axi_m_r       (man_r[man_port_idx][sub_port_idx]),
          .i_axi_m_r_valid (man_r_valid[man_port_idx][sub_port_idx]),
          .o_axi_m_r_ready (man_r_ready[man_port_idx][sub_port_idx])
        );

      end else begin : gen_no_con
        localparam logic [43:0] NoConnectionErrorData = {36'hDEAD_CAB1E, sub_port_idx[0+:8]};

        axe_axi_err_sub #(
          .AxiIdWidth  (SubAxiIdWidth),
          .Resp        (axi_pkg::RespDecErr),
          .ReadData    (NoConnectionErrorData),
          .MaxTxn      (4),
          .SupportAtops(SupportAtops),
          .axi_aw_t    (axi_s_aw_t),
          .axi_w_t     (axi_w_t),
          .axi_b_t     (axi_s_b_t),
          .axi_ar_t    (axi_s_ar_t),
          .axi_r_t     (axi_s_r_t)
        ) u_axe_axi_err_sub (
          .i_clk,
          .i_rst_n,

          .i_axi_s_aw      (sub_aw[sub_port_idx][man_port_idx]),
          .i_axi_s_aw_valid(sub_aw_valid[sub_port_idx][man_port_idx]),
          .o_axi_s_aw_ready(sub_aw_ready[sub_port_idx][man_port_idx]),
          .i_axi_s_w       (sub_w[sub_port_idx][man_port_idx]),
          .i_axi_s_w_valid (sub_w_valid[sub_port_idx][man_port_idx]),
          .o_axi_s_w_ready (sub_w_ready[sub_port_idx][man_port_idx]),
          .o_axi_s_b       (sub_b[sub_port_idx][man_port_idx]),
          .o_axi_s_b_valid (sub_b_valid[sub_port_idx][man_port_idx]),
          .i_axi_s_b_ready (sub_b_ready[sub_port_idx][man_port_idx]),
          .i_axi_s_ar      (sub_ar[sub_port_idx][man_port_idx]),
          .i_axi_s_ar_valid(sub_ar_valid[sub_port_idx][man_port_idx]),
          .o_axi_s_ar_ready(sub_ar_ready[sub_port_idx][man_port_idx]),
          .o_axi_s_r       (sub_r[sub_port_idx][man_port_idx]),
          .o_axi_s_r_valid (sub_r_valid[sub_port_idx][man_port_idx]),
          .i_axi_s_r_ready (sub_r_ready[sub_port_idx][man_port_idx])
        );

        always_comb man_aw[man_port_idx][sub_port_idx]       = '0;
        always_comb man_aw_valid[man_port_idx][sub_port_idx] = '0;
        always_comb man_w[man_port_idx][sub_port_idx]        = '0;
        always_comb man_w_valid[man_port_idx][sub_port_idx]  = '0;
        always_comb man_b_ready[man_port_idx][sub_port_idx]  = '0;
        always_comb man_ar[man_port_idx][sub_port_idx]       = '0;
        always_comb man_ar_valid[man_port_idx][sub_port_idx] = '0;
        always_comb man_r_ready[man_port_idx][sub_port_idx]  = '0;
      end
    end
  end

  for (genvar man_port_idx = 0; man_port_idx < NumManPorts; man_port_idx++) begin : gen_man_mux
    axe_axi_mux #(
      .NumPorts     (NumSubPorts),
      .SubAxiIdWidth(SubAxiIdWidth),
      .MaxTxn       (MaxManTxn),
      .FallThrough  (FallThrough),
      .CutAw        (LatencyMode[4]),
      .CutW         (LatencyMode[3]),
      .CutB         (LatencyMode[2]),
      .CutAr        (LatencyMode[1]),
      .CutR         (LatencyMode[0]),
      .axi_s_aw_t   (axi_s_aw_t),
      .axi_m_aw_t   (axi_m_aw_t),
      .axi_w_t      (axi_w_t),
      .axi_s_b_t    (axi_s_b_t),
      .axi_m_b_t    (axi_m_b_t),
      .axi_s_ar_t   (axi_s_ar_t),
      .axi_m_ar_t   (axi_m_ar_t),
      .axi_s_r_t    (axi_s_r_t),
      .axi_m_r_t    (axi_m_r_t)
    ) u_axi_mux (
      .i_clk,
      .i_rst_n,

      .i_axi_s_aw      (man_aw[man_port_idx]),
      .i_axi_s_aw_valid(man_aw_valid[man_port_idx]),
      .o_axi_s_aw_ready(man_aw_ready[man_port_idx]),
      .i_axi_s_w       (man_w[man_port_idx]),
      .i_axi_s_w_valid (man_w_valid[man_port_idx]),
      .o_axi_s_w_ready (man_w_ready[man_port_idx]),
      .o_axi_s_b       (man_b[man_port_idx]),
      .o_axi_s_b_valid (man_b_valid[man_port_idx]),
      .i_axi_s_b_ready (man_b_ready[man_port_idx]),
      .i_axi_s_ar      (man_ar[man_port_idx]),
      .i_axi_s_ar_valid(man_ar_valid[man_port_idx]),
      .o_axi_s_ar_ready(man_ar_ready[man_port_idx]),
      .o_axi_s_r       (man_r[man_port_idx]),
      .o_axi_s_r_valid (man_r_valid[man_port_idx]),
      .i_axi_s_r_ready (man_r_ready[man_port_idx]),

      .o_axi_m_aw      (o_axi_m_aw[man_port_idx]),
      .o_axi_m_aw_valid(o_axi_m_aw_valid[man_port_idx]),
      .i_axi_m_aw_ready(i_axi_m_aw_ready[man_port_idx]),
      .o_axi_m_w       (o_axi_m_w[man_port_idx]),
      .o_axi_m_w_valid (o_axi_m_w_valid[man_port_idx]),
      .i_axi_m_w_ready (i_axi_m_w_ready[man_port_idx]),
      .i_axi_m_b       (i_axi_m_b[man_port_idx]),
      .i_axi_m_b_valid (i_axi_m_b_valid[man_port_idx]),
      .o_axi_m_b_ready (o_axi_m_b_ready[man_port_idx]),
      .o_axi_m_ar      (o_axi_m_ar[man_port_idx]),
      .o_axi_m_ar_valid(o_axi_m_ar_valid[man_port_idx]),
      .i_axi_m_ar_ready(i_axi_m_ar_ready[man_port_idx]),
      .i_axi_m_r       (i_axi_m_r[man_port_idx]),
      .i_axi_m_r_valid (i_axi_m_r_valid[man_port_idx]),
      .o_axi_m_r_ready (o_axi_m_r_ready[man_port_idx])
    );
  end
endmodule
