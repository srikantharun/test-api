// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Generate the actual datapath instructions from the command stream
///
module dwpu_dp_instr_shim #(
  /// Number of operands the DWPU is configured for
  parameter int unsigned NumOperands = dwpu_pkg::NUM_OPERANDS,
  /// Add a output pipeline register
  parameter bit PipelineOutput = 1'b0
)(
  /// Clock, positive edge triggered
  input  wire  i_clk, // ASO-UNUSED_INPUT : Clock is needed for optional pipeline
  /// Asynchronous reset, active low
  input  wire  i_rst_n, // ASO-UNUSED_INPUT : Reset is needed for optional pipeline

  /// Instruction data custom to the block using the command generator
  input  dwpu_pkg::dwpu_dp_command_t           i_dp_command_data,
  /// Command metadata stattic per command
  input  aic_dp_cmd_gen_pkg::metadata_t        i_dp_command_metadata, // ASO-UNUSED_INPUT : Not all metadata is needed. DWPu has no vector mode, reserved.
  /// Command iteration data specific to the datapath command
  input  aic_dp_cmd_gen_pkg::loop_iterations_t i_dp_command_iterations, // ASO-UNUSED_INPUT : Only overall last is used from loop iterations.
  /// This is the last datapath command for this command
  input  logic                                 i_dp_command_last,
  /// The datapath command is valid flag
  input  logic                                 i_dp_command_valid,
  /// The ready flag for this datapath command
  output logic                                 o_dp_command_ready,

  /// DP instruction stream tdata
  output dwpu_pkg::dp_instruction_t o_dp_instruction_tdata,
  /// DP instruction stream tlast flag
  output logic                      o_dp_instruction_tlast,
  /// DP instruction stream tvalid flag
  output logic                      o_dp_instruction_tvalid,
  /// DP instruction stream tready flag
  input  logic                      i_dp_instruction_tready
);
  ////////////////////////////////////////
  // Translate command into Instruction //
  ////////////////////////////////////////
  dwpu_pkg::dp_instruction_t dp_instruction_data;

  always_comb begin
    dp_instruction_data = '{
      bypass:         i_dp_command_metadata.format == aic_dp_cmd_gen_pkg::Bypass,
      command:        i_dp_command_data
    };
    // Apply weight offset if applicable:
    for (int unsigned i = 0; i < NumOperands; i++) begin
      dp_instruction_data.command.w_sel[i] = dwpu_pkg::w_sel_t'(i_dp_command_data.w_sel[i] + i_dp_command_metadata.extra);
    end

    // only push the last in the data channel if we are at the last instruction
    dp_instruction_data.command.op_desc.last_push = i_dp_command_data.op_desc.last_push & i_dp_command_iterations.overall_last; // ASO-MULTI_ASSIGN : overwrite
  end

  /////////////////////////
  // Register the Output //
  /////////////////////////
  if (PipelineOutput) begin : gen_output_pipe
    cc_stream_reg #(
      .data_t(logic[dwpu_pkg::DP_INSTRUCTION_WIDTH:0])
    ) u_dp_cmd_reg (
      .i_clk,
      .i_rst_n,
      .i_flush   (1'b0),
      .i_data    ({i_dp_command_last, dp_instruction_data}),
      .i_valid   (i_dp_command_valid),
      .o_ready   (o_dp_command_ready),
      .o_data    ({o_dp_instruction_tlast, o_dp_instruction_tdata}),
      .o_valid   (o_dp_instruction_tvalid),
      .i_ready   (i_dp_instruction_tready)
    );
  end else begin : gen_output_conn
    always_comb o_dp_instruction_tdata  =   dp_instruction_data;
    always_comb o_dp_instruction_tlast  = i_dp_command_last;
    always_comb o_dp_instruction_tvalid = i_dp_command_valid;
    always_comb o_dp_command_ready      = i_dp_instruction_tready;
  end
endmodule
