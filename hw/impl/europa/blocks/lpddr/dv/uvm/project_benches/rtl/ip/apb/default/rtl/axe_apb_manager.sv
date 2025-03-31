// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// APB bus manager.
// Creates APB transactions in response to operations on tap
// i_apb_valid will trigger the generation of a new transaction
// if o_apb_ready is 1.
// i_apb_wr_req=1 will trigger a write transaction, i_apb_wr_req=0
// will trigger a read transaction.

module axe_apb_manager #(
  // width definition for APB address bus
  parameter int  unsigned PAW               = 16                        ,
  // width definition for APB data bus
  parameter int  unsigned PDW               = 32                        ,
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW            = 4                         ,
  // APB types
  parameter type          paddr_t       = logic [PAW              -1:0] ,
  parameter type          pdata_t       = logic [PDW              -1:0] ,
  parameter type          pstrb_t       = logic [PSTRBW           -1:0]
)(
  // Clock, positive edge triggered
  input  wire                         i_clk                      ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n                    ,

  // APB manager interface
  output paddr_t                      o_apb_m_paddr              ,
  output pdata_t                      o_apb_m_pwdata             ,
  output logic                        o_apb_m_pwrite             ,
  output logic                        o_apb_m_psel               ,
  output logic                        o_apb_m_penable            ,
  output pstrb_t                      o_apb_m_pstrb              ,
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot              ,
  input  logic                        i_apb_m_pready             ,
  input  pdata_t                      i_apb_m_prdata             ,
  input  logic                        i_apb_m_pslverr            ,

  // I/f to DW tap -> all signal synchronized to i_clk
  // read requiest
  input  logic                        i_apb_valid                ,
  input  logic                        i_apb_wr_req               ,
  input  paddr_t                      i_apb_address              ,
  input  pdata_t                      i_apb_wdata                ,
  input  pstrb_t                      i_apb_pstrb                ,
  output pdata_t                      o_apb_rdata                ,
  output logic                        o_apb_error                ,
  output logic                        o_apb_ready
);

//==============================================================================
// Local parameters
// pprot value will be constant as follows:
// +-----+--------+-------------------+
// | BIT |  Value | Description       |
// +-----+--------+-------------------+
// |  0  |    0   | Normal access     |
// |  1  |    1   | non-secure access |
// |  2  |    0   | Data access       |
// +-----+--------+-------------------+
localparam axe_apb_pkg::apb_prot_t PPROT_VAL =  3'h2;

//==============================================================================
// types
// APB state type
typedef enum { APB_IDLE, APB_SETUP, APB_ENABLE } apb_state_e;

//==============================================================================
// signal declarations
apb_state_e state_q;
apb_state_e state_d;

//==============================================================================
// RTL

// APB IF state controlled outputs
always_comb begin
  o_apb_m_psel            = 1'b0;
  o_apb_m_penable         = 1'b0;
  o_apb_m_pprot           = PPROT_VAL;
  o_apb_ready             = 1'b0;

  unique case(state_q)
    APB_IDLE    : begin
      o_apb_ready         = 1'b1;
    end
    APB_SETUP   : begin
      o_apb_m_psel        = 1'h1;
    end
    APB_ENABLE  : begin
      o_apb_m_psel        = 1'h1;
      o_apb_m_penable     = 1'h1;
      o_apb_ready         = i_apb_m_pready;
    end
    default : /* keep default values */;
  endcase
end

// Sample control signals upon valid request
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    o_apb_m_paddr  <= '0;
    o_apb_m_pwdata <= '0;
    o_apb_m_pwrite <= '0;
    o_apb_m_pstrb  <= '0;
  end else begin
    if (o_apb_ready && i_apb_valid) begin
      o_apb_m_paddr  <= i_apb_address;
      o_apb_m_pwdata <= i_apb_wdata;
      o_apb_m_pwrite <= i_apb_wr_req;
      o_apb_m_pstrb  <= i_apb_pstrb;
    end
  end
end

//==============================================================================
// APB manager state machine
always_comb begin
  state_d = state_q;

  unique case(state_q)
    APB_IDLE    : begin
      if (i_apb_valid) state_d = APB_SETUP;
      else             state_d = APB_IDLE;
    end
    // APB_SETUP -> single cycle
    // set APB address phase signals
    APB_SETUP   : begin
      state_d = APB_ENABLE;
    end
    // APB_ENABLE -> leave when pready input is set unless there is an error
    APB_ENABLE  : begin
      if (i_apb_m_pready) begin
        if (i_apb_valid) state_d = APB_SETUP;
        else             state_d = APB_IDLE;
      end else begin
        state_d = APB_ENABLE;
      end
    end
    default : begin
      state_d = APB_IDLE;
    end
  endcase
end

// state register
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    state_q <= APB_IDLE;
  end else begin
    state_q <= state_d;
  end
end

always_comb o_apb_rdata = i_apb_m_prdata;
always_comb o_apb_error = i_apb_m_pslverr;

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
