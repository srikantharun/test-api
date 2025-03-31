// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// The *token unit* is responsible to synchronize handshakes and stall the execution unit.
///
/// It uses the respective stream fork/join from the *common cell library*.
/// Which respective synchronization unit is connected to the execute is determined by a valid token instruction opcode.
///
/// !!! note "Token Mask"
///
///     The token mask is shared between local andglobal tokens.  However depending on module parameterization only
///     the LSBs of the respective mask are looked at.  If this unit gets a valid token handshake from execute, but no bit
///     in the token mask is set, the handshake will be interpreted as completed and execute towards the upstream.
///     The instruction validation is making sure however that thiscondition should never happen.
///
///
/// ![AIC_CD_TOKEN_UNIT: Block-Diagram](./figures/aic_token_unit.drawio.svg)
///
module aic_cd_token_unit #(
  /// The number of local tokens
  parameter int unsigned NumLocalTokens = 0,
  /// The number of global tokens
  parameter int unsigned NumGlobalTokens = 0
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ////////////
  // Status //
  ////////////
  /// Unit is busy
  output logic o_busy,

  ///////////////////
  // Token Request //
  ///////////////////
  /// The token opcode
  input  aic_cd_pkg::token_opcode_e i_token_opcode,
  /// The mask which lines to trigger
  input  aic_cd_pkg::token_mask_t   i_token_mask,
  /// The request is valid
  input  logic                      i_token_valid,
  /// The request is ready / Has been done
  output logic                      o_token_ready,

  ///////////////////////
  // Local Token Lines //
  ///////////////////////
  output logic [NumLocalTokens-1:0] o_token_local_prod_valid,
  input  logic [NumLocalTokens-1:0] i_token_local_prod_ready,

  input  logic [NumLocalTokens-1:0] i_token_local_cons_valid,
  output logic [NumLocalTokens-1:0] o_token_local_cons_ready,

  ////////////////////////
  // Global Token Lines //
  ////////////////////////
  output logic [NumGlobalTokens-1:0] o_token_global_prod_valid,
  input  logic [NumGlobalTokens-1:0] i_token_global_prod_ready,

  input  logic [NumGlobalTokens-1:0] i_token_global_cons_valid,
  output logic [NumGlobalTokens-1:0] o_token_global_cons_ready
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  if (NumLocalTokens  == 0) $fatal(1, "Parameter: 'NumLocalTokens' must be larger than 0;");
  if (NumGlobalTokens == 0) $fatal(1, "Parameter: 'NumGlobalTokens' must be larger than 0;");

  if (NumLocalTokens  > aic_cd_pkg::TOKEN_MASK_WIDTH)
      $fatal(1, "Parameter: 'NumLocalTokens' maximum value is %d; actual: %d",
             aic_cd_pkg::TOKEN_MASK_WIDTH, NumLocalTokens);
  if (NumGlobalTokens > aic_cd_pkg::TOKEN_MASK_WIDTH)
      $fatal(1, "Parameter: 'NumGlobalTokens' maximum value is %d; actual: %d",
             aic_cd_pkg::TOKEN_MASK_WIDTH, NumGlobalTokens);

  localparam int unsigned UsedMaskWidth = (NumGlobalTokens > NumLocalTokens) ? NumGlobalTokens : NumLocalTokens;
  typedef logic [NumLocalTokens -1:0] token_local_mask_t;
  typedef logic [NumGlobalTokens-1:0] token_global_mask_t;

  ////////////
  // Status //
  ////////////
  always_comb o_busy = i_token_valid;

  ////////////////////////////////
  // The Stream Forks and joins //
  ////////////////////////////////

  logic token_local_prod_valid;
  logic token_local_prod_ready;
  cc_stream_fork #(
    .NumStreams(NumLocalTokens)
  ) u_local_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(token_local_mask_t'(i_token_mask)),
    .i_valid (token_local_prod_valid),
    .o_ready (token_local_prod_ready),
    .o_valid (o_token_local_prod_valid),
    .i_ready (i_token_local_prod_ready)
  );

  logic token_local_cons_valid;
  logic token_local_cons_ready;
  cc_stream_join #(
    .NumStreams(NumLocalTokens)
  ) u_local_join (
    .i_select(token_local_mask_t'(i_token_mask)),
    .i_valid (i_token_local_cons_valid),
    .o_ready (o_token_local_cons_ready),
    .o_valid (token_local_cons_valid),
    .i_ready (token_local_cons_ready)
  );

  logic token_global_prod_valid;
  logic token_global_prod_ready;
  cc_stream_fork #(
    .NumStreams(NumGlobalTokens)
  ) u_global_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(token_global_mask_t'(i_token_mask)),
    .i_valid (token_global_prod_valid),
    .o_ready (token_global_prod_ready),
    .o_valid (o_token_global_prod_valid),
    .i_ready (i_token_global_prod_ready)
  );

  logic token_global_cons_valid;
  logic token_global_cons_ready;
  cc_stream_join #(
    .NumStreams(NumGlobalTokens)
  ) u_global_join (
    .i_select(token_global_mask_t'(i_token_mask)),
    .i_valid (i_token_global_cons_valid),
    .o_ready (o_token_global_cons_ready),
    .o_valid (token_global_cons_valid),
    .i_ready (token_global_cons_ready)
  );

  ////////////////////////////////////////////////////
  // Connect the Handshakes according to the Opcode //
  ////////////////////////////////////////////////////

  logic token_local_mask_is_sane;
  logic token_global_mask_is_sane;
  always_comb token_local_mask_is_sane  = |token_local_mask_t'(i_token_mask);
  always_comb token_global_mask_is_sane = |token_global_mask_t'(i_token_mask);

  always_comb begin
    o_token_ready           = 1'b0;
    token_local_cons_ready  = 1'b0;
    token_local_prod_valid  = 1'b0;
    token_global_cons_ready = 1'b0;
    token_global_prod_valid = 1'b0;

    if (i_token_valid) begin
      unique case (i_token_opcode)
        aic_cd_pkg::TokenConsumeLocal: begin
          if (!token_local_mask_is_sane) o_token_ready = 1'b1;
          else begin
            token_local_cons_ready = 1'b1;
            o_token_ready          = token_local_cons_valid;
          end
        end
        aic_cd_pkg::TokenProduceLocal: begin
          if (!token_local_mask_is_sane) o_token_ready = 1'b1;
          else begin
            token_local_prod_valid = 1'b1;
            o_token_ready          = token_local_prod_ready;
          end
        end
        aic_cd_pkg::TokenConsumeGlobal: begin
          if (!token_global_mask_is_sane) o_token_ready = 1'b1;
          else begin
            token_global_cons_ready = 1'b1;
            o_token_ready           = token_global_cons_valid;
          end
        end
        aic_cd_pkg::TokenProduceGlobal: begin
          if (!token_global_mask_is_sane) o_token_ready = 1'b1;
          else begin
            token_global_prod_valid = 1'b1;
            o_token_ready           = token_global_prod_ready;
          end
        end
        default: o_token_ready = 1'b1;
      endcase
    end
  end
endmodule
