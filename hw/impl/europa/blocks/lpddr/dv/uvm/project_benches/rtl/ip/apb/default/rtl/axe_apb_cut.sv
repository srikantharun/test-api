// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Cut all combinational paths between the subordinate and manager port.
///
/// Due to the protocol this will half the throughput of this bus!
///
module axe_apb_cut #(
  /// Width of the APB address (only used for typedef)
  parameter int unsigned ApbAddrWidth = 16,
  /// Width of the APB data (only used for typedef)
  parameter int unsigned ApbDataWidth = 32,
  /// Width of the APB strobe
  localparam int unsigned ApbStbWidth = ApbDataWidth / 8,
  /// APB address type
  parameter type  paddr_t = logic[ApbAddrWidth-1:0],
  /// APB data type
  parameter type  pdata_t = logic[ApbDataWidth-1:0],
  /// APB strobe type
  parameter type  pstrb_t = logic[ApbStbWidth-1:0]
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /////////////////
  // Subordinate //
  /////////////////
  input  paddr_t                      i_apb_s_paddr,
  input  pdata_t                      i_apb_s_pwdata,
  input  logic                        i_apb_s_pwrite,
  input  logic                        i_apb_s_psel,
  input  logic                        i_apb_s_penable,
  input  pstrb_t                      i_apb_s_pstrb,
  input  axe_apb_pkg::apb_prot_t      i_apb_s_pprot,
  output logic                        o_apb_s_pready,
  output pdata_t                      o_apb_s_prdata,
  output logic                        o_apb_s_pslverr,
  /////////////
  // Manager //
  /////////////
  output paddr_t                      o_apb_m_paddr,
  output pdata_t                      o_apb_m_pwdata,
  output logic                        o_apb_m_pwrite,
  output logic                        o_apb_m_psel,
  output logic                        o_apb_m_penable,
  output pstrb_t                      o_apb_m_pstrb,
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot,
  input  logic                        i_apb_m_pready,
  input  pdata_t                      i_apb_m_prdata,
  input  logic                        i_apb_m_pslverr
);

  //////////////////////////
  // Flops to cut the bus //
  //////////////////////////
  logic load_request;
  logic load_response;

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)     begin
      o_apb_m_paddr   <= paddr_t'(0);
      o_apb_m_pwdata  <= pdata_t'(0);
      o_apb_m_pwrite  <= 1'b0;
      o_apb_m_pstrb   <= pstrb_t'(0);
      o_apb_m_pprot   <= axe_apb_pkg::apb_prot_t'(0);
    end else if (load_request)  begin
      o_apb_m_paddr   <= i_apb_s_paddr;
      o_apb_m_pwdata  <= i_apb_s_pwdata;
      o_apb_m_pwrite  <= i_apb_s_pwrite;
      o_apb_m_pstrb   <= i_apb_s_pstrb;
      o_apb_m_pprot   <= i_apb_s_pprot;
    end
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)    begin
      o_apb_s_prdata  <= pdata_t'(0);
      o_apb_s_pslverr <= 1'b0;
    end else if (load_response) begin
      o_apb_s_prdata  <= i_apb_m_prdata;
      o_apb_s_pslverr <= i_apb_m_pslverr;
    end
  end

  /////////
  // FSM //
  /////////
  typedef enum logic[1:0] {
    SETUP,
    REQUEST,
    CAPTURE,
    RESPOND
  } state_e;
  state_e state_q, state_d;

  always_comb begin
    state_d         = state_q;
    load_request    = 1'b0;
    load_response   = 1'b0;
    o_apb_m_psel    = 1'b0;
    o_apb_m_penable = 1'b0;
    o_apb_s_pready  = 1'b0;

    unique case (state_q)
      SETUP: begin
        if (i_apb_s_psel) begin
          load_request = 1'b1;
          state_d      = REQUEST;
        end
      end
      REQUEST: begin
        o_apb_m_psel = 1'b1;
        state_d      = CAPTURE;
      end
      CAPTURE: begin
        o_apb_m_psel    = 1'b1;
        o_apb_m_penable = 1'b1;
        if (i_apb_m_pready) begin
          load_response = 1'b1;
          state_d       = RESPOND;
        end
      end
      RESPOND: begin
        o_apb_s_pready = 1'b1;
        state_d        = SETUP;
      end
      default: state_d = SETUP;
    endcase
  end

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) state_q <= SETUP;
    else          state_q <= state_d;
  end
endmodule
