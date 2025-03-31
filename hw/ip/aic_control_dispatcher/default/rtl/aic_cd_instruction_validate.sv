// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Validate data fetched from the memory and translate it into `aic_cd` instructions
///
/// The instruction validation acts as a gate keeper.  Making sure that only sanely formulated instructions are allowed to
/// be dispached to execute.  It also is responsible of adding the instruction index to the respective instruction to keep
/// it traceable as it traverses the system.  It further synchronizes the instruction metadata `control_offset` from
/// the command and attachesit to theemmited instruction stream.
///
/// ![AIC_CD_INSTRUCTION_VALIDATE: Block Diagram](./figures/aic_cd_instruction_validate.drawio.svg)
///
///
/// For control it uses a simple FSM which handles the handshaking as well as the dropping of the task list if there
/// was an error encountered.
///
///
/// ## Validation
///
/// ::: hw/ip/aic_control_dispatcher/default/rtl/pkg/aic_cd_pkg.sv:aic_cd_pkg.instruction_validation_errors_t
///
///
/// ## Error Behaviour: Task List Dropping
///
/// There are two mechanism at play which can cause a task list to be rejected.
///
/// 1. The Validation fails due to a malformed instruction.
/// 2. The downstream sub-units detected a dynamic error duringexecution.
///
/// Both cases will cause the current validated task-list stream to be dropped!  This dropping happens from the current
/// instruction being validated.  The second case will make it a bit hard to predict how many instructions are currently
/// in-flight as there are various pipelines and stalling points present in the downstream microarchitecture.
/// The error reporting the CSR will report the instruction index which caused the error.  It gived priority to
/// instructions further down the pipeline.
///
/// The dropping is implemented at this point, becuase here is the last stage where we can cleanly drop the instruction
/// stream before it gets distributed to all the sub-units.
///
/// !!! note 'In Flight Instructions'
///
///     Any instrcution which passes the validation from this unit is considered *in-flight* and will attemt to finish
///     executing.  So even is a previous instruction downstrean in the pieline causes a task-list to be dropped, the
///     `AIC_CD` will finish executing the already dispacthed instruction to the execution unit.
///
module aic_cd_instruction_validate #(
  /// The number of destinations the unit interacts with
  parameter int unsigned NumDestinations = 17,
  /// The number of Patch Mode entries
  parameter int unsigned NumPatchModeEntries = 8,
  /// The number of Patch Table entries
  parameter int unsigned NumPatchTableEntries = 16,
  /// The number of local tokens
  parameter int unsigned NumLocalTokens = 17,
  /// The number of global tokens
  parameter int unsigned NumGlobalTokens = 1,
  /// The AXI R channel type
  parameter type axi_r_t = aic_cd_defaults_pkg::axi_m_r_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ///////////////////////////////////////////
  // Instruction Metadata from the Command //
  ///////////////////////////////////////////
  /// The expected amount of instructions
  input  aic_cd_pkg::task_list_word_length_t i_metadata_task_list_length,
  /// The controll offset from the command
  input  aic_cd_pkg::control_offset_t   i_metadata_control_offset,
  /// The metadata is valid
  input  logic                          i_metadata_valid,
  /// We are ready for the metadata
  output logic                          o_metadata_ready,

  ///////////////////////////////
  // Data from the AXI channel //
  ///////////////////////////////
  /// The response data from the AXI channel
  input  axi_r_t i_response_r,
  /// The response is valid
  input  logic   i_response_r_valid,
  /// The response is ready
  output logic   o_response_r_ready,

  ///////////////////////////////////////////
  // Control Dispatcher Instruction Stream //
  ///////////////////////////////////////////
  /// The fetched and validated instruction
  output aic_cd_pkg::instruction_t    o_instruction,
  /// The control offset belonging to this instruction
  output aic_cd_pkg::control_offset_t o_instruction_control_offset,
  /// This is the last instruction of this respective command
  output logic                        o_instruction_last,
  /// This instruction is valid
  output logic                        o_instruction_valid,
  /// Ready flag for the instruction
  input  logic                        i_instruction_ready,

  /////////////////
  // Observation //
  /////////////////
  /// The unit is busy doing something
  output logic                               o_busy,
  /// The current instruction index (starts at 1)
  output aic_cd_pkg::task_list_word_length_t o_instruction_index,
  /// An instrcution is emitted
  output logic                               o_instruction_emitted,
  /// An instruction was dropped
  output logic                               o_instruction_dropped,

  ////////////////////////
  // Instruction Errors //
  ////////////////////////
  /// An error occured downstream, go into error state and drop everything
  input  logic                                       i_drop_instructions,
  /// The validation encountered an error
  output aic_cd_pkg::instruction_validation_errors_t o_validation_errors
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  if (aic_cd_pkg::INSTRUCTION_WIDTH != $bits(i_response_r.data))
      $fatal(1, "Parameter: 'aic_cd_pkg::INSTRUCTION_WIDTH' must match data width of the AXI read channel;");

  if (NumPatchModeEntries > 2**aic_cd_pkg::PATCH_MODE_WIDTH)
      $fatal(1, "Parameter: 'NumPatchModeEntries' must be not larger than '2**aic_cd_pkg::PATCH_MODE_WIDTH';");

  if (NumPatchTableEntries > 2**aic_cd_pkg::PATCH_ID_WIDTH)
      $fatal(1, "Parameter: 'NumPatchTableEntries' must be not larger than '2**aic_cd_pkg::PATCH_ID_WIDTH';");

  if (NumLocalTokens  == 0) $fatal(1, "Parameter: 'NumLocalTokens' must be larger than 0;");
  if (NumGlobalTokens == 0) $fatal(1, "Parameter: 'NumGlobalTokens' must be larger than 0;");

  if (NumLocalTokens  > aic_cd_pkg::TOKEN_MASK_WIDTH)
      $fatal(1, "Parameter: 'NumLocalTokens' maximum value is %d; actual: %d",
             aic_cd_pkg::TOKEN_MASK_WIDTH-1, NumLocalTokens);
  if (NumGlobalTokens > aic_cd_pkg::TOKEN_MASK_WIDTH)
      $fatal(1, "Parameter: 'NumGlobalTokens' maximum value is %d; actual: %d",
             aic_cd_pkg::TOKEN_MASK_WIDTH-1, NumGlobalTokens);

  /////////////////////////////////////////////
  // Count the Instructions for flag Setting //
  /////////////////////////////////////////////

  logic instruction_counter_enable;
  logic instruction_counter_load;

  always_comb instruction_counter_enable = o_instruction_emitted | o_instruction_dropped;

  cc_cnt_delta #(
    .Width         (aic_cd_pkg::TASK_LIST_LENGTH_WIDTH),
    .StickyOverflow(1'b0)
  ) u_instruction_counter (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (instruction_counter_enable),
    .i_cnt_down(1'b0),
    .i_delta   (aic_cd_pkg::task_list_word_length_t'(1)),
    .o_q       (o_instruction_index),
    .i_d       (aic_cd_pkg::task_list_word_length_t'(1)),
    .i_d_load  (instruction_counter_load),
    .o_overflow(/* not used */)
  );

  //////////////////////
  // Error Conditions //
  //////////////////////

  aic_cd_pkg::instruction_t instruction_from_data;
  always_comb instruction_from_data.view_vector = i_response_r.data;

  aic_cd_pkg::opcode_e extracted_opcode;
  always_comb extracted_opcode = aic_cd_pkg::get_opcode(instruction_from_data);

  // Extract the token mapping (1-bit wider than needed because SV can't cope with null ranges...)
  logic [aic_cd_pkg::TOKEN_MASK_WIDTH:0] extracted_token_mask;
  always_comb extracted_token_mask = {1'b0, instruction_from_data.view_token.token_mask};

  aic_cd_pkg::instruction_validation_errors_t validation_errors;
  always_comb validation_errors = '{
    axi_response_slverr:        i_response_r.resp == axi_pkg::RespSlvErr,
    axi_response_decerr:        i_response_r.resp == axi_pkg::RespDecErr,
    destination_id_mapping:     extracted_opcode inside {aic_cd_pkg::OpcodeCommand, aic_cd_pkg::OpcodeProgram}
                            &  (instruction_from_data.view_command.dst_id >= aic_cd_pkg::destination_id_t'(NumDestinations)),
    patch_mode_mapping:         extracted_opcode inside {aic_cd_pkg::OpcodeCommand}
                            &  (instruction_from_data.view_command.patch_mode >= aic_cd_pkg::patch_mode_t'(NumPatchModeEntries)),
    patch_id_0_mapping:         extracted_opcode inside {aic_cd_pkg::OpcodeCommand}
                            &  (instruction_from_data.view_command.patch_id_0 >= aic_cd_pkg::patch_id_t'(NumPatchTableEntries)),
    patch_id_1_mapping:         extracted_opcode inside {aic_cd_pkg::OpcodeCommand}
                            &  (instruction_from_data.view_command.patch_id_1 >= aic_cd_pkg::patch_id_t'(NumPatchTableEntries)),
    token_illegal_opcode:       extracted_opcode inside {aic_cd_pkg::OpcodeToken}
                            & !(instruction_from_data.view_token.token_opcode inside {
                                    aic_cd_pkg::TokenConsumeLocal, aic_cd_pkg::TokenConsumeGlobal,
                                    aic_cd_pkg::TokenProduceLocal, aic_cd_pkg::TokenProduceGlobal}),
    token_local_map_empty:      extracted_opcode inside {aic_cd_pkg::OpcodeToken}
                            &   instruction_from_data.view_token.token_opcode inside {aic_cd_pkg::TokenProduceLocal, aic_cd_pkg::TokenConsumeLocal}
                            & ~|extracted_token_mask[0+:NumLocalTokens],
    token_global_map_empty:     extracted_opcode inside {aic_cd_pkg::OpcodeToken}
                            &   instruction_from_data.view_token.token_opcode inside {aic_cd_pkg::TokenProduceGlobal, aic_cd_pkg::TokenConsumeGlobal}
                            & ~|extracted_token_mask[0+:NumGlobalTokens],
    token_local_mapping:        extracted_opcode inside {aic_cd_pkg::OpcodeToken}
                            &   instruction_from_data.view_token.token_opcode inside {aic_cd_pkg::TokenProduceLocal, aic_cd_pkg::TokenConsumeLocal}
                            &  |extracted_token_mask[aic_cd_pkg::TOKEN_MASK_WIDTH:NumLocalTokens],
    token_global_mapping:       extracted_opcode inside {aic_cd_pkg::OpcodeToken}
                            &   instruction_from_data.view_token.token_opcode inside {aic_cd_pkg::TokenProduceGlobal, aic_cd_pkg::TokenConsumeGlobal}
                            &  |extracted_token_mask[aic_cd_pkg::TOKEN_MASK_WIDTH:NumGlobalTokens],
    default: 1'b0
  };

  ////////////////////////////////////
  // Instruction Validation Control //
  ////////////////////////////////////

  logic instruction_disconnect;
  logic instruction_drop;

  typedef enum logic [1:0] {
    IDLE,
    ERROR,
    BUSY
  } state_e;
  state_e state_q, state_d;
  logic   change_state;

  always_comb o_busy =
      i_metadata_valid
    | state_q inside {BUSY, ERROR};

  always_comb begin
    state_d      = state_q;
    change_state = 1'b0;

    o_metadata_ready = 1'b0;

    instruction_counter_load = 1'b0;
    instruction_disconnect   = 1'b1;
    instruction_drop         = 1'b0;

    o_validation_errors = '{default: 1'b0};

    unique case (state_q)
      IDLE: begin
        if (i_metadata_valid) begin
          instruction_counter_load = 1'b1;
          state_d                  = BUSY;
          change_state             = 1'b1;
        end
      end
      BUSY: begin
        if ((|validation_errors) || i_drop_instructions) begin
          o_validation_errors = validation_errors;
          state_d             = ERROR;
          change_state        = 1'b1;
        end else begin
          instruction_disconnect = 1'b0;
          if (o_instruction_emitted && o_instruction_last) begin
            state_d          = IDLE;
            change_state     = 1'b1;
            o_metadata_ready = 1'b1;
          end
        end
      end
      ERROR: begin
        // Wait until we are done then go back to idle
        instruction_drop = 1'b1;
        if (o_instruction_dropped && o_instruction_last) begin
          state_d          = IDLE;
          change_state     = 1'b1;
          o_metadata_ready = 1'b1;
        end
      end
      default: begin
        state_d      = IDLE;
        change_state = 1'b1;
      end
    endcase
  end

  ///////////////////////
  // Handshake Connect //
  ///////////////////////

  cc_stream_disconnect #(
    .data_t(aic_cd_pkg::instruction_t)
  ) u_stream_disconnect (
    .i_disconnect (instruction_disconnect),
    .i_drop       (instruction_drop),
    .o_dropped    (o_instruction_dropped),
    .o_transaction(o_instruction_emitted),
    .i_data       (instruction_from_data),
    .i_valid      (i_response_r_valid),
    .o_ready      (o_response_r_ready),
    .o_data       (o_instruction),
    .o_valid      (o_instruction_valid),
    .i_ready      (i_instruction_ready)
  );

  always_comb o_instruction_control_offset = i_metadata_control_offset;
  always_comb o_instruction_last           = i_metadata_task_list_length == o_instruction_index;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          state_q <= IDLE;
    else if (change_state) state_q <= state_d;
  end

endmodule
