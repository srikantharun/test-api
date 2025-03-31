// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Cut the handshaking and data
///
module ocp_lite_cut #(
  /// The address
  parameter type addr_t = logic[0:0],
  /// The data
  parameter type data_t = logic[0:0]
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,
  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  logic  i_s_mcmd,
  input  addr_t i_s_maddr,
  input  data_t i_s_mdata,
  output logic  o_s_scmd_accept,
  //////////////////
  // Manager Port //
  //////////////////
  output logic  o_m_mcmd,
  output addr_t o_m_maddr,
  output data_t o_m_mdata,
  input  logic  i_m_scmd_accept
);

  typedef struct packed {
    addr_t addr;
    data_t data;
  } spill_data_t;

  spill_data_t spill_inp_data;
  spill_data_t spill_oup_data;

  always_comb spill_inp_data = '{
    addr: i_s_maddr,
    data: i_s_mdata
  };

  cc_stream_spill_reg #(
    .data_t  (spill_data_t),
    .Bypass  (1'b0),
    .CutFirst(1'b0)
  ) u_cc_stream_spill_reg (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (spill_inp_data),
    .i_valid(i_s_mcmd),
    .o_ready(o_s_scmd_accept),
    .o_data (spill_oup_data),
    .o_valid(o_m_mcmd),
    .i_ready(i_m_scmd_accept)
  );

  always_comb o_m_maddr = spill_oup_data.addr;
  always_comb o_m_mdata = spill_oup_data.data;
endmodule
