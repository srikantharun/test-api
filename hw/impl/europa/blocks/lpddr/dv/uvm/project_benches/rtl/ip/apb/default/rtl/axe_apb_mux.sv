// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

module axe_apb_mux #(
  // numbe of APB masters
  parameter int  unsigned NB_APBIN          = 2                          ,
  // width definition for APB address bus
  parameter int  unsigned PAW               = 16                         ,
  // width definition for APB data bus
  parameter int  unsigned PDW               = 32                         ,
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW            = 4                          ,
  // APB types
  parameter type          paddr_t       = logic           [PAW     -1:0] ,
  parameter type          pdata_t       = logic           [PDW     -1:0] ,
  parameter type          pstrb_t       = logic           [PSTRBW  -1:0] ,
  localparam int unsigned IDX_W         = (NB_APBIN > 32'd1) ? unsigned'($clog2(NB_APBIN)) : 32'd1,
  localparam type         m_idx_t       = logic [IDX_W-1:0]
) (
  // Clock, positive edge triggered
  input  wire                         i_clk                          ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n                        ,

  // APB input interfaces
  input  paddr_t                  i_apb_s_paddr[NB_APBIN],
  input  pdata_t                  i_apb_s_pwdata[NB_APBIN],
  input  logic                    i_apb_s_pwrite[NB_APBIN],
  input  logic                    i_apb_s_psel[NB_APBIN],
  input  logic                    i_apb_s_penable[NB_APBIN],
  input  pstrb_t                  i_apb_s_pstrb[NB_APBIN],
  input  axe_apb_pkg::apb_prot_t  i_apb_s_pprot[NB_APBIN],
  output logic                    o_apb_s_pready[NB_APBIN],
  output pdata_t                  o_apb_s_prdata[NB_APBIN],
  output logic                    o_apb_s_pslverr[NB_APBIN],
  // APB output interface
  output paddr_t                  o_apb_m_paddr,
  output pdata_t                  o_apb_m_pwdata,
  output logic                    o_apb_m_pwrite,
  output logic                    o_apb_m_psel,
  output logic                    o_apb_m_penable,
  output pstrb_t                  o_apb_m_pstrb,
  output axe_apb_pkg::apb_prot_t  o_apb_m_pprot,
  input  logic                    i_apb_m_pready,
  input  pdata_t                  i_apb_m_prdata,
  input  logic                    i_apb_m_pslverr,
  // Selected manager signal (optional)
  output m_idx_t                  o_manager_idx
);

//==============================================================================
// Local parameters
// APB acccess grant type
typedef  logic [NB_APBIN-1:0] packed_apbin_t;

//==============================================================================
// signal declarations
packed_apbin_t    packed_apb_s_psel;
packed_apbin_t    packed_apb_s_pready;
logic             apb_m_granted;
m_idx_t           nxt_arb_idx;
m_idx_t           arb_idx_sampled;
m_idx_t           arb_idx;
logic             transaction_end;
logic             transaction_end_q;
logic             transaction_start;
logic             apb_m_psel_q;

//==============================================================================
// RTL
//==============================================================================

always_comb packed_apb_s_psel = {<< {i_apb_s_psel}};

// Static arbitration, 0 being the highest priority index
rr_arb_tree #(
  .NumIn     (NB_APBIN),
  .datatype_t(logic),
  .ExtPrio   (1'b1),
  .AxiVldRdy (1'b1),
  .LockIn    (1'b0),
  .FairArb   (1'b1)
) u_apb_mux_arb (
  .i_clk    (i_clk),
  .i_rst_n  (i_rst_n),
  .flush_i  (1'b0),
  .rr_i     ('0),
  .req_i    (packed_apb_s_psel),
  .gnt_o    (packed_apb_s_pready),
  .data_i   ('0),
  .gnt_i    (apb_m_granted),
  .req_o    (o_apb_m_psel),
  .data_o   (/*open*/),
  .idx_o    (nxt_arb_idx)
);

// Transaction on the output port finishing, 1-cycle pulse.
always_comb transaction_end = o_apb_m_penable & i_apb_m_pready;
// Transaction on the output port starting, 1-cycle pulse.
always_comb transaction_start = o_apb_m_psel && !o_apb_m_penable;
// Request on the output port is granted if pready & penable are set.
always_comb apb_m_granted = i_apb_m_pready & o_apb_m_penable;

always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    transaction_end_q <= 1'b0;
    apb_m_psel_q      <= 1'b0;
    arb_idx_sampled   <= '0;
  end else begin
    transaction_end_q <= transaction_end;
    apb_m_psel_q      <= o_apb_m_psel;
    if (transaction_start)
      arb_idx_sampled <= nxt_arb_idx;
  end
end

always_comb arb_idx = transaction_start ? nxt_arb_idx : arb_idx_sampled;

//==============================================================================
// APB mux

always_comb begin

  // penable should always be set 1 cycle after the start of a new transaction
  // Always set penable 1 cycle after psel.
  // Always clear penable for 1 cycle after the end of a transaction in case of
  // back to back transactions.
  o_apb_m_penable = o_apb_m_psel & apb_m_psel_q & ~transaction_end_q;

  o_apb_m_paddr   = i_apb_s_paddr   [arb_idx];
  o_apb_m_pwdata  = i_apb_s_pwdata  [arb_idx];
  o_apb_m_pwrite  = i_apb_s_pwrite  [arb_idx];
  o_apb_m_pstrb   = i_apb_s_pstrb   [arb_idx];
  o_apb_m_pprot   = i_apb_s_pprot   [arb_idx];

  for (int unsigned i = 0; i < NB_APBIN; i++) begin
    o_apb_s_pready  [i] = packed_apb_s_pready[i];
    o_apb_s_prdata  [i] = (i == arb_idx) ? i_apb_m_prdata  : '0;
    o_apb_s_pslverr [i] = (i == arb_idx) ? i_apb_m_pslverr & packed_apb_s_pready[i] : '0;
  end

  o_manager_idx = arb_idx;

end

//==============================================================================
// SVA

`ifdef ASSERTIONS_ON
  // Once asserted, PSEL and PENABLE shall be stable until PREADY=1
  psel_pready_handshake     : assert property (axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, o_apb_m_psel, i_apb_m_pready));
  penable_pready_handshake  : assert property (axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, o_apb_m_penable, i_apb_m_pready));
  // PSEL can deassert only if PREADY=1 in the previous cycle
  psel_deassert             : assert property (axe_dv_properties_pkg::p_valid_ready_deassert(i_clk, i_rst_n, o_apb_m_psel, i_apb_m_pready));
  // When PENABLE=1, control signals shall be stable until PREADY=1
  paddr_stable              : assert property (axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_apb_m_penable, i_apb_m_pready, o_apb_m_paddr));
  pwdata_stable             : assert property (axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_apb_m_penable, i_apb_m_pready, o_apb_m_pwdata));
  pwrite_stable             : assert property (axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_apb_m_penable, i_apb_m_pready, o_apb_m_pwrite));
  pstrb_stable              : assert property (axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_apb_m_penable, i_apb_m_pready, o_apb_m_pstrb));
  pprot_stable              : assert property (axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_apb_m_penable, i_apb_m_pready, o_apb_m_pprot));
  // PENABLE shall always rise 1 cycle after PSEL rises
  penable_rise              : assert property (apb_properties_pkg::p_penable_rise(i_clk, i_rst_n, o_apb_m_psel, o_apb_m_penable, i_apb_m_pready));
`endif

endmodule
