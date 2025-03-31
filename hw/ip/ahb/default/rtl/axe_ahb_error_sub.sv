// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// AHB error subordinate.
/// Used to respond to transfers to undefined regions of memory, where no AHB subordinates are mapped.
/// - A zero wait OKAY response is made to IDLE or BUSY transfers
/// - An ERROR response is made to NONSEQUENTIAL or SEQUENTIAL transfers.
module axe_ahb_error_sub
  import axe_ahb_pkg::*;
#(
  /// Width definition for AHB address bus
  parameter int  unsigned HAW           = 16,
  /// Width definition for AHB data bus
  parameter int  unsigned HDW           = 32,
  /// AHB types
  parameter type          haddr_t       = logic [HAW -1:0],
  parameter type          hdata_t       = logic [HDW -1:0]

) (
  /// Clock, positive edge triggered
  input  wire                 i_clk,
  /// Asynchronous reset, active low
  input  wire                 i_rst_n,
  ///////////////////////////////////
  /// AHB input interface signals ///
  ///////////////////////////////////
  input  htrans_e             i_ahb_s_htrans,
  input  logic                i_ahb_s_hsel,
  input  logic                i_ahb_s_hready,
  output logic                o_ahb_s_hreadyout,
  output logic                o_ahb_s_hresp
);

// -----------------------------------------------------------------------------
// signal declarations
// -----------------------------------------------------------------------------
typedef enum logic[1:0] { IDLE, ERROR0, ERROR1 } ahb_sub_state_e;

ahb_sub_state_e state_d;
ahb_sub_state_e state_q;
logic valid_in_transaction;

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------

always_comb valid_in_transaction = i_ahb_s_hsel & i_ahb_s_hready & ((i_ahb_s_htrans == NONSEQ) | (i_ahb_s_htrans == SEQ));


always_ff @( posedge i_clk or negedge i_rst_n ) begin
  if (!i_rst_n) begin
    state_q <= IDLE;
  end else begin
    state_q <= state_d;
  end
end

always_comb begin
  state_d = state_q;
  o_ahb_s_hreadyout = 1'b1;
  o_ahb_s_hresp     = 1'b0;

  unique case (state_q)
    IDLE: begin
      if (valid_in_transaction)
        state_d = ERROR0;
    end
    ERROR0: begin
      o_ahb_s_hreadyout = 1'b0;
      o_ahb_s_hresp     = 1'b1;
      state_d = ERROR1;
    end
    ERROR1: begin
      o_ahb_s_hresp = 1'b1;
      state_d = IDLE;
    end
    default: /*Keep default values*/ ;
  endcase
end

endmodule
