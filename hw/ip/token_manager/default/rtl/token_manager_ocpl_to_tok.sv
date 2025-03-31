// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token manager OCPL to token_lines
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module token_manager_ocpl_to_tok #(
  // TOP
  parameter int unsigned MaxNrTokens = 0,
  parameter int unsigned NrTokens = 0,
  //// Top mapping producer to device:
  parameter int TopMapConsToDev[MaxNrTokens] = '{default: 0}
)(
  input  wire i_clk,
  input  wire i_rst_n,

  // top info:
  input  logic [token_manager_pkg::TOKEN_MANAGER_MAX_VUID:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_uid_to_vuid,

  // Top connection via OCPL:
  input  logic        i_ocpl_s_mcmd,
  output logic        o_ocpl_s_scmdaccept,
  input  logic [7:0]  i_ocpl_s_mdata,

    // local connections for top:
  output logic [NrTokens-1:0] o_cons_valid,
  input  logic [NrTokens-1:0] i_cons_ready
);

  logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] vuid, uid;

  // UID to VUID lookup for the Virtual Consumer
  always_comb uid = i_ocpl_s_mdata[token_manager_pkg::TOKEN_MANAGER_UID_W-1:0];
  always_comb vuid = i_uid_to_vuid[uid];

  // Map vuid to consumer token lines:
  always_comb begin
    o_cons_valid = 0; // default
    o_ocpl_s_scmdaccept = 1'b0;
    for (int c=0; c<NrTokens; c++) begin
      if (vuid == TopMapConsToDev[c]) begin
        o_cons_valid[c] = i_ocpl_s_mcmd;
        o_ocpl_s_scmdaccept = i_cons_ready[c];
      end
    end
  end

endmodule
