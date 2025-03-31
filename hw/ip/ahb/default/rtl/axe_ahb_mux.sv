// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// AHB mux between NB_AHBIN input managers and a single AHB output.
module axe_ahb_mux
  import axe_ahb_pkg::*;
#(
  /// Number of AHB managers
  parameter int  unsigned NB_AHBIN      = 2,
  /// Width definition for AHB address bus
  parameter int  unsigned HAW           = 16,
  /// Width definition for AHB data bus
  parameter int  unsigned HDW           = 32,
  /// 1: select static arbitration
  /// 0: select round robin arbitration
  parameter bit           STATIC_ARB    = 1,
  /// AHB address type
  parameter type          haddr_t       = logic [HAW -1:0],
  /// AHB data type
  parameter type          hdata_t       = logic [HDW -1:0]

) (
  /// Clock, positive edge triggered
  input  wire                         i_clk,
  /// Asynchronous reset, active low
  input  wire                         i_rst_n,
  ////////////////////////////
  /// AHB input interfaces ///
  ////////////////////////////
  input  haddr_t              i_ahb_s_haddr[NB_AHBIN],
  input  logic                i_ahb_s_hwrite[NB_AHBIN],
  input  hdata_t              i_ahb_s_hwdata[NB_AHBIN],
  input  htrans_e             i_ahb_s_htrans[NB_AHBIN],
  input  hburst_e             i_ahb_s_hburst[NB_AHBIN],
  input  hsize_e              i_ahb_s_hsize[NB_AHBIN],
  output hdata_t              o_ahb_s_hrdata[NB_AHBIN],
  output logic                o_ahb_s_hready[NB_AHBIN],
  output logic                o_ahb_s_hresp[NB_AHBIN],
  ////////////////////////////
  /// AHB output interface ///
  ////////////////////////////
  output haddr_t              o_ahb_m_haddr,
  output logic                o_ahb_m_hwrite,
  output hdata_t              o_ahb_m_hwdata,
  output htrans_e             o_ahb_m_htrans,
  output hburst_e             o_ahb_m_hburst,
  output hsize_e              o_ahb_m_hsize,
  input  hdata_t              i_ahb_m_hrdata,
  input  logic                i_ahb_m_hready,
  input  logic                i_ahb_m_hresp
);

// -----------------------------------------------------------------------------
// Local parameters
// -----------------------------------------------------------------------------
// AHB acccess grant type
//
localparam int unsigned IDX_W = (NB_AHBIN > 32'd1) ? unsigned'($clog2(NB_AHBIN)) : 32'd1;
localparam int unsigned LAST_IDX = NB_AHBIN-1;

typedef  logic [NB_AHBIN-1:0] packed_ahbin_t;
typedef  logic [IDX_W-1:0]    m_idx_t;
typedef  logic [IDX_W  :0]    m_prio_idx_t;

// -----------------------------------------------------------------------------
// signal declarations
// -----------------------------------------------------------------------------
//
packed_ahbin_t    request_array;
packed_ahbin_t    locked_array;
packed_ahbin_t    grant_array;
m_idx_t           arb_idx;
logic             request;
logic             grant;

haddr_t           ahb_s_haddr  [NB_AHBIN];
logic             ahb_s_hwrite [NB_AHBIN];
hdata_t           ahb_s_hwdata [NB_AHBIN];
htrans_e          ahb_s_htrans [NB_AHBIN];
hburst_e          ahb_s_hburst [NB_AHBIN];
hsize_e           ahb_s_hsize  [NB_AHBIN];
hdata_t           ahb_s_hrdata [NB_AHBIN];
logic             ahb_s_hready [NB_AHBIN];
logic             ahb_s_hresp  [NB_AHBIN];

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------
//
// The following modules stalls incoming AHB managers transactions whenever the
// downstream is busy with another transaction.
// The stall module will keep the manager stalled while i_locked is 0.
// The stall module is notified of the end of a transaction via i_granted.
//
for (genvar j=0;  unsigned'(j)<NB_AHBIN; j++) begin : g_ahb_stall
  axe_ahb_stall #(
    .HAW    (HAW),
    .HDW    (HDW)
  ) u_axe_ahb_stall (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_ahb_s_haddr    (i_ahb_s_haddr  [j]),
    .i_ahb_s_hwrite   (i_ahb_s_hwrite [j]),
    .i_ahb_s_hwdata   (i_ahb_s_hwdata [j]),
    .i_ahb_s_htrans   (i_ahb_s_htrans [j]),
    .i_ahb_s_hburst   (i_ahb_s_hburst [j]),
    .i_ahb_s_hsize    (i_ahb_s_hsize  [j]),
    .o_ahb_s_hrdata   (o_ahb_s_hrdata [j]),
    .o_ahb_s_hready   (o_ahb_s_hready [j]),
    .o_ahb_s_hresp    (o_ahb_s_hresp  [j]),
    .o_ahb_m_haddr    (ahb_s_haddr    [j]),
    .o_ahb_m_hwrite   (ahb_s_hwrite   [j]),
    .o_ahb_m_hwdata   (ahb_s_hwdata   [j]),
    .o_ahb_m_htrans   (ahb_s_htrans   [j]),
    .o_ahb_m_hburst   (ahb_s_hburst   [j]),
    .o_ahb_m_hsize    (ahb_s_hsize    [j]),
    .i_ahb_m_hrdata   (ahb_s_hrdata   [j]),
    .i_ahb_m_hready   (ahb_s_hready   [j]),
    .i_ahb_m_hresp    (ahb_s_hresp    [j]),
    .o_req            (request_array  [j]),
    .i_granted        (grant_array    [j]),
    .i_locked         (locked_array   [j])
  );
end

rr_arb_tree #(
  .NumIn     (NB_AHBIN),
  .datatype_t(logic),
  .ExtPrio   (STATIC_ARB),
  .AxiVldRdy (1'b1),
  .LockIn    (1'b1),
  .FairArb   (1'b1)
) u_apb_mux_arb (
  .i_clk    (i_clk),
  .i_rst_n  (i_rst_n),
  .flush_i  (1'b0),
  .rr_i     ('0),
  .req_i    (request_array),
  .gnt_o    (grant_array),
  .data_i   ('0),
  .gnt_i    (grant),
  .req_o    (request),
  .data_o   (/*open*/),
  .idx_o    (arb_idx)
);

always_comb locked_array = packed_ahbin_t'(request) << arb_idx;
always_comb grant = i_ahb_m_hready & (o_ahb_m_htrans == axe_ahb_pkg::IDLE);

// -----------------------------------------------------------------------------
// AHB mux
// -----------------------------------------------------------------------------

always_comb begin
  o_ahb_m_haddr   = ahb_s_haddr  [arb_idx];
  o_ahb_m_hwrite  = ahb_s_hwrite [arb_idx];
  o_ahb_m_htrans  = ahb_s_htrans [arb_idx];
  o_ahb_m_hburst  = ahb_s_hburst [arb_idx];
  o_ahb_m_hsize   = ahb_s_hsize  [arb_idx];
  o_ahb_m_hwdata  = ahb_s_hwdata [arb_idx];
  // Signals to AHB input ports
  for (int unsigned i = 0; i < NB_AHBIN; i++) begin
    ahb_s_hready  [i] = (i == arb_idx) ? i_ahb_m_hready  : 1'b0;
    ahb_s_hrdata  [i] = (i == arb_idx) ? i_ahb_m_hrdata  : '0;
    ahb_s_hresp   [i] = (i == arb_idx) ? i_ahb_m_hresp   : '0;
  end
end

`ifndef SYNTHESIS
`ifdef ASSERTIONS_ON
property sva_double_request;
  @(posedge i_clk)
  disable iff (!i_rst_n)
    (request_array == '1 ##[1:$] request_array == '0);
endproperty

sva_double_request_cover: cover property (sva_double_request);
`endif
`endif

endmodule
