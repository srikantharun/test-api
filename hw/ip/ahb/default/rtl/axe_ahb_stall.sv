// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// AHB stall.
/// This block stalls the input AHB bus (ahb_s) whenever the downstream
/// is not ready to accept a new transaction (i_locked == 0).
/// The downstream is notified that a new transaction is present via o_req.
/// If the downstream is ready to accept the transaction, it will assert i_locked.
/// Once the downstream completes the transaction, it will assert i_granted.
module axe_ahb_stall
  import axe_ahb_pkg::*;
#(
  /// Width definition for AHB address bus
  parameter int  unsigned HAW           = 16,
  /// Width definition for AHB data bus
  parameter int  unsigned HDW           = 32,
  /// AHB address type
  parameter type          haddr_t       = logic [HAW -1:0],
  /// AHB data type
  parameter type          hdata_t       = logic [HDW -1:0]

) (
  /// Clock, positive edge triggered
  input  wire                 i_clk,
  /// Asynchronous reset, active low
  input  wire                 i_rst_n,
  ////////////////////////////
  /// AHB input interfaces ///
  ////////////////////////////
  input  haddr_t              i_ahb_s_haddr,
  input  logic                i_ahb_s_hwrite,
  input  hdata_t              i_ahb_s_hwdata,
  input  htrans_e             i_ahb_s_htrans,
  input  hburst_e             i_ahb_s_hburst,
  input  hsize_e              i_ahb_s_hsize,
  output hdata_t              o_ahb_s_hrdata,
  output logic                o_ahb_s_hready,
  output logic                o_ahb_s_hresp,
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
  input  logic                i_ahb_m_hresp,
  /// AHB request to arbiter
  output logic                o_req,
  /// AHB request done from arbiter
  input  logic                i_granted,
  /// AHB request locked from arbiter
  input  logic                i_locked
);

// -----------------------------------------------------------------------------
// signal declarations
// -----------------------------------------------------------------------------

logic                sample_req;
// Sampled address-phase signals of transfers that must be stalled.
haddr_t              ahb_m_haddr_q;
logic                ahb_m_hwrite_q;
htrans_e             ahb_m_htrans_q;
hburst_e             ahb_m_hburst_q;
hsize_e              ahb_m_hsize_q;

typedef enum logic [1:0] { AHB_IDLE, AHB_STALLED, AHB_LOCKED } ahb_stall_state_e;
ahb_stall_state_e state_d, state_q;

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------

always_comb begin

  state_d = state_q;
  sample_req = 1'b0;
  o_req      = 1'b0;

  o_ahb_m_haddr  = i_ahb_s_haddr;
  o_ahb_m_hwrite = i_ahb_s_hwrite;
  o_ahb_m_htrans = i_ahb_s_htrans;
  o_ahb_m_hburst = i_ahb_s_hburst;
  o_ahb_m_hsize  = i_ahb_s_hsize;
  o_ahb_m_hwdata = i_ahb_s_hwdata;
  // OKAY response
  o_ahb_s_hrdata  = hdata_t'(0);
  o_ahb_s_hresp   = 1'b0;
  o_ahb_s_hready  = 1'b1;

  unique case (state_q)
    AHB_IDLE: begin
      if (i_ahb_s_htrans == NONSEQ) begin
        o_req = 1'b1;
        if (i_locked) begin
          state_d = AHB_LOCKED;
        end else begin
          state_d = AHB_STALLED;
          sample_req = 1'b1;
        end
      end
    end
    AHB_STALLED: begin
      o_req = 1'b1;
      if (i_locked) state_d = AHB_LOCKED;
      o_ahb_m_haddr   = ahb_m_haddr_q;
      o_ahb_m_hwrite  = ahb_m_hwrite_q;
      o_ahb_m_htrans  = ahb_m_htrans_q;
      o_ahb_m_hburst  = ahb_m_hburst_q;
      o_ahb_m_hsize   = ahb_m_hsize_q;
      // Insert wait state
      o_ahb_s_hrdata  = hdata_t'(0);
      o_ahb_s_hresp   = 1'b0;
      o_ahb_s_hready  = 1'b0;
    end
    AHB_LOCKED: begin
      o_req = 1'b1;
      o_ahb_s_hrdata = i_ahb_m_hrdata;
      o_ahb_s_hresp  = i_ahb_m_hresp;
      o_ahb_s_hready = i_ahb_m_hready;
      if (i_granted) state_d = AHB_IDLE;
    end
    default: /*Keep default values*/;
  endcase

end

always_ff @(posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) state_q <= AHB_IDLE;
  else          state_q <= state_d;
end

always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    ahb_m_haddr_q  <= '0;
    ahb_m_hwrite_q <= '0;
    ahb_m_htrans_q <= IDLE;
    ahb_m_hburst_q <= SINGLE;
    ahb_m_hsize_q  <= BYTE;
  end else begin
    if (sample_req) begin
      ahb_m_haddr_q  <= i_ahb_s_haddr;
      ahb_m_hwrite_q <= i_ahb_s_hwrite;
      ahb_m_htrans_q <= i_ahb_s_htrans;
      ahb_m_hburst_q <= i_ahb_s_hburst;
      ahb_m_hsize_q  <= i_ahb_s_hsize;
    end
  end
end

endmodule
