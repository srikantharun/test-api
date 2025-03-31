// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Integrated Synchronization Cell
///
module axe_tcl_seq_sync #(
  /// Number of synchronization stages
  parameter int unsigned SyncStages = 3,
  /// Reset value
  parameter bit ResetValue = 0,
  /// The probability of metastability, see axe_tcl_seq_metastability_model
  parameter int unsigned Ratio = 99
)(
  /// Clock to synchronize to, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc async
  /// Data input
  input  logic i_d,
  // doc sync i_clk
  /// Synchronized data output
  output logic o_q
);
  // Wire to the metastability model, in synth is output.
  wire reg_q;

  case (SyncStages)
    2: begin : gen_stages_2
      case (ResetValue)
        0: begin : gen_rst_val_0
          wire rst;

          INV_D1_N_S6TR_C54L08 u_tc_lib_seq_inv (
            .Y(rst),
            .A(i_rst_n)
          );

          // This cell has an active high reset!
          SDFFYRPQ2DRLV_D1_N_S6TL_C54L08 u_tc_lib_seq_sync (
            .Q (reg_q),
            .CK(i_clk),
            .D (i_d),
            .R (rst),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SE(1'b0),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SI(1'b0)
          );
        end
        1: begin : gen_rst_val_0
          SDFFYSQ2DRLV_D1_N_S6TL_C54L08 u_tc_lib_seq_sync (
            .Q (reg_q),
            .CK(i_clk),
            .D (i_d),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SE(1'b0),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SI(1'b0),
            .SN(i_rst_n)
          );
        end
      endcase
    end
    3: begin : gen_stages_3
      case (ResetValue)
        0: begin : gen_rst_val_0
          wire rst;

          INV_D1_N_S6TR_C54L08 u_tc_lib_seq_inv (
            .Y(rst),
            .A(i_rst_n)
          );

          // This cell has an active high reset!
          SDFFYRPQ3DRLV_D1_N_S6TL_C54L08 u_tc_lib_seq_sync (
            .Q (reg_q),
            .CK(i_clk),
            .D (i_d),
            .R (rst),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SE(1'b0),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SI(1'b0)
          );
        end
        1: begin : gen_rst_val_0
          SDFFYSQ3DRLV_D1_N_S6TL_C54L08 u_tc_lib_seq_sync (
            .Q (reg_q),
            .CK(i_clk),
            .D (i_d),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SE(1'b0),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SI(1'b0),
            .SN(i_rst_n)
          );
        end
      endcase
    end
    4: begin : gen_stages_4
      case (ResetValue)
        0: begin : gen_rst_val_0
          wire rst;

          INV_D1_N_S6TR_C54L08 u_tc_lib_seq_inv (
            .Y(rst),
            .A(i_rst_n)
          );

          // This cell has an active high reset!
          SDFFYRPQ4DRLV_D1_N_S6TL_C54L08 u_tc_lib_seq_sync (
            .Q (reg_q),
            .CK(i_clk),
            .D (i_d),
            .R (rst),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SE(1'b0),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SI(1'b0)
          );
        end
        1: begin : gen_rst_val_0
          SDFFYSQ4DRLV_D1_N_S6TL_C54L08 u_tc_lib_seq_sync (
            .Q (reg_q),
            .CK(i_clk),
            .D (i_d),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SE(1'b0),
            // TODO(@wolfgang.roenninger): Add audit as this has to stay open
            .SI(1'b0),
            .SN(i_rst_n)
          );
        end
      endcase
    end
    default: begin : gen_stages_fatal
      $fatal(1, "Not supported SyncStages [2-4]: is %d", SyncStages);
    end
  endcase

  `ifndef SYNTHESIS
    axe_tcl_seq_metastability_model #(
      .ResetValue(ResetValue),
      .Ratio     (Ratio)
    ) u_metastability_model (
      .i_clk,
      .i_rst_n,
      .i_q    (reg_q),
      .o_q
    );
  `else
    assign o_q = reg_q;
  `endif
endmodule
