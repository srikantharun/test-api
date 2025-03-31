// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***

/// Multicut the handshaking and data
///
module ocp_lite_multicut #(
  /// Number of cuts.
  parameter int unsigned NumCuts = 32'd1,
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

  logic  cut_mcmd[NumCuts+1];
  addr_t cut_maddr[NumCuts+1];
  data_t cut_mdata[NumCuts+1];
  logic  cut_scmd_accept[NumCuts+1];

  // connect subordinate to the lowest index
  always_comb cut_mcmd[0] = i_s_mcmd;
  always_comb cut_maddr[0] = i_s_maddr;
  always_comb cut_mdata[0] = i_s_mdata;
  always_comb o_s_scmd_accept = cut_scmd_accept[0];

  // OCP_lite cuts
  for (genvar i = 0; i < NumCuts; i++) begin : gen_ocp_lite_cuts
    ocp_lite_cut #(
      .addr_t(addr_t),
      .data_t(data_t)
    ) u_ocp_lite_cut (
      .i_clk,
      .i_rst_n,

      .i_s_mcmd(cut_mcmd[i]),
      .i_s_maddr(cut_maddr[i]),
      .i_s_mdata(cut_mdata[i]),
      .o_s_scmd_accept(cut_scmd_accept[i]),

      .o_m_mcmd(cut_mcmd[i+1]),
      .o_m_maddr(cut_maddr[i+1]),
      .o_m_mdata(cut_mdata[i+1]),
      .i_m_scmd_accept(cut_scmd_accept[i+1])
    );
  end

  // connect manager to the highest index
  always_comb o_m_mcmd = cut_mcmd[NumCuts];
  always_comb o_m_maddr = cut_maddr[NumCuts];
  always_comb o_m_mdata = cut_mdata[NumCuts];
  always_comb cut_scmd_accept[NumCuts] = i_m_scmd_accept;

endmodule
