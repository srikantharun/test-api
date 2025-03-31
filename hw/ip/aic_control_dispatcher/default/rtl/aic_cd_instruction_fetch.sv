// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Depending on command fetches instructions and makes them available as a stream.
///
/// The instruction fetch unit is responsible for fetching the task list.  For this it converts the recieved command into
/// respective AXI read transactions.  The read data is then validated to garantee sanity of the fetched instructions of
/// the task list.
///
/// !!! warinng "Invalid Instruction Behaviour"
///
///     If an instruction is deemed non valid it and all subsequent instructions are dropped at the validatiuon stage.
///     This means the `aic_cd` will always fetch the full task list, but might stop executing halfway when there was
///     an issue detected.  This also applies for errors occuring in the downstream units.  If the `aic_cd` decides to drop
///     a task list execution it happens in the validation stage.
///
/// ![AIC_CD_INSTRUCTION_FETCH: Block Diagram](./figures/aic_cd_instruction_fetch.drawio.svg)
///
/// The *instruction fetch* (`aic_cd_instruction_fetch`) is comprised of different sub-units which perform one task only.
/// The details of each sub-unit can be found on their respective pages. The units are:
///
/// - [Instruction Request](request.md): Converts Commands to a stream of AXI AR Like requests. These fitt already
///   onto the AR channel, however are not yet AXI protocol conform. The axi read unit takes care of this.
/// - [AXI Read Unit](../axi_units.md#axi-read-unit-aic_cd_axi_read): Takes in an AR Like request and break it up into
///   AXI conform transactions. Has internal buffer
///   space for the response data and only requests data which it also can buffer directly.
/// - [Instruction Validate](validate.md): Merges the metadata information from the command with the fetched instruction
///   data and performs validation on it.
///
/// Additionally the `command_offset` as well as the `task list length` fields from the command are propagated as well as
/// static sideband signals.  They flow parallel to the fetched instructions are are synchronized to the validated
/// instructions.
///
module aic_cd_instruction_fetch #(
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
  /// The Axi ID width of the AXI AR channel
  parameter int unsigned AxiIdWidth = aic_cd_defaults_pkg::AXI_M_ID_WIDTH,
  /// The Concrete AXI ID to use
  parameter logic [AxiIdWidth-1:0] AxiIdForFetch = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(0),
  /// The Address width of the AXI AR channel
  parameter int unsigned AxiAddrWidth = aic_cd_defaults_pkg::AXI_M_ADDR_WIDTH,
  /// The depth of the instruction buffer.
  parameter int unsigned InstructionBufferDepth = 16,
  /// The AXI AR channel type
  parameter type axi_ar_t = aic_cd_defaults_pkg::axi_m_ar_t,
  /// The AXI R channel type
  parameter type axi_r_t = aic_cd_defaults_pkg::axi_m_r_t,
  /// Use a memory for the buffer
  parameter bit BufferUsesMacro = 1'b1,
  /// Memory Implementation Key
  parameter MemImplKey = "default",
  /// Sideband input signal type to tc_sram
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
)(
  ///////////////////
  // Clock / Reset //
  ///////////////////
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ////////////////////////////////////////////
  // Control quasi stattic siganls from CSR //
  ////////////////////////////////////////////
  /// The global address offset that must be added to all copy transactions
  input  axi_pkg::axi_largest_addr_t  i_aic_base_addr,
  /// The offset to the source data which is added to all copy transaction reads
  input  axi_pkg::axi_largest_addr_t  i_ctrl_data_base_addr,

  ///////////////////////////
  // Command Block Command //
  ///////////////////////////
  /// The overall command from the command block
  input  aic_cd_pkg::aic_cd_command_t i_command,
  /// The command is valid
  input  logic                        i_command_valid,
  /// we are ready for a command
  output logic                        o_command_ready,

  /////////////////////////
  // AXI Manager AR Port //
  /////////////////////////
  /// The AR channel payload
  output axi_ar_t o_axi_m_ar,
  /// The AR channel payload
  output logic    o_axi_m_ar_valid,
  /// The AR channel payload
  input  logic    i_axi_m_ar_ready,
  /// The AR channel payload
  input  axi_r_t  i_axi_m_r,
  /// The AR channel payload
  input  logic    i_axi_m_r_valid,
  /// The AR channel payload
  output logic    o_axi_m_r_ready,

  ///////////////////////////////////////////
  // Control Dispatcher Instruction Stream //
  ///////////////////////////////////////////
  /// The fetched and validated instruction
  output aic_cd_pkg::instruction_t           o_instruction,
  /// The control offset belonging to this instruction
  output aic_cd_pkg::control_offset_t        o_instruction_control_offset,
  /// The index of the transaction
  output aic_cd_pkg::task_list_word_length_t o_instruction_index,
  /// This is the last instruction of this respective command
  output logic                               o_instruction_last,
  /// This instruction is valid
  output logic                               o_instruction_valid,
  /// Ready flag for the instruction
  input  logic                               i_instruction_ready,

  ///////////////////////
  // Errors and Status //
  ///////////////////////
  /// An error occured downstream, go into error state and drop everything
  input  logic                                       i_drop_instructions,
  /// The instruction request is busy
  output logic                                       o_request_busy,
  /// The AXI read manager is busy
  output logic                                       o_axi_read_busy,
  /// The validation is busy
  output logic                                       o_validation_busy,
  /// The task list command is empty, has zero length
  output logic                                       o_error_empty_task_list,
  /// The instruction validation encountered an error
  output aic_cd_pkg::instruction_validation_errors_t o_error_instruction_validation,

  /////////////////////////////
  // Memory Sideband Signals //
  /////////////////////////////
  /// Memory sideband input signals (tie to `'0` if `BufferUsesMacro == 1'b0`)
  input  ram_impl_inp_t i_ram_impl,
  /// Memory sideband output signals
  output ram_impl_oup_t o_ram_impl
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  if ($bits(o_instruction) != $bits(i_axi_m_r.data)) $fatal(1, "Instruction width must match AXI Data Width;");

  ///////////////////////////////////////////////////////////////////////////////////////
  // Split the command up                                                              //
  // the metadata is forwarded to when the instruction data comes back from the Memory //
  ///////////////////////////////////////////////////////////////////////////////////////

  logic [1:0] command_select;
  logic [1:0] command_valid;
  logic [1:0] command_ready;

  always_comb begin
    command_select[0] = 1'b1;
    // Only forward metadata if length is not 0
    command_select[1] = (i_command.view_struct.task_list_length != aic_cd_pkg::task_list_word_length_t'(0));
  end

  cc_stream_fork #(
    .NumStreams(2)
  ) u_command_cc_sream_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(command_select),
    .i_valid (i_command_valid),
    .o_ready (o_command_ready),
    .o_valid (command_valid),
    .i_ready (command_ready)
  );

  aic_cd_pkg::task_list_word_length_t metadata_task_list_length;
  aic_cd_pkg::control_offset_t   metadata_control_offset;
  logic                          metadata_valid;
  logic                          metadata_ready;

  cc_stream_spill_reg #(
    .DataWidth(aic_cd_pkg::TASK_LIST_LENGTH_WIDTH + aic_cd_pkg::CONTROL_OFFSET_WIDTH)
  ) u_metadate_spill_reg (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({i_command.view_struct.control_offset, i_command.view_struct.task_list_length}),
    .i_valid(command_valid[1]),
    .o_ready(command_ready[1]),
    .o_data ({metadata_control_offset, metadata_task_list_length}),
    .o_valid(metadata_valid),
    .i_ready(metadata_ready)
  );

  ////////////////////////////////////
  // Form the Overall Fetch Request //
  ////////////////////////////////////
  axi_ar_t request_ar;
  logic    request_ar_valid;
  logic    request_ar_ready;

  aic_cd_instruction_request #(
    .AxiIdWidth   (AxiIdWidth),
    .AxiIdForFetch(AxiIdForFetch),
    .AxiAddrWidth (AxiAddrWidth),
    .axi_ar_t    (axi_ar_t)
  ) u_aic_cd_instruction_request (
    .i_clk,
    .i_rst_n,
    .i_aic_base_addr,
    .i_ctrl_data_base_addr,
    .o_busy                      (o_request_busy),
    .o_error_empty_task_list,
    .i_command,
    .i_command_valid             (command_valid[0]),
    .o_command_ready             (command_ready[0]),
    .o_request_ar                (request_ar),
    .o_request_ar_valid          (request_ar_valid),
    .i_request_ar_ready          (request_ar_ready)
  );

  ////////////////////////////////////////////
  // Fetch the Instructions from the Memory //
  ////////////////////////////////////////////
  axi_r_t response_r;
  logic   response_r_valid;
  logic   response_r_ready;

  aic_cd_axi_read #(
    .AxiAddrWidth   (AxiAddrWidth),
    .ReadBufferDepth(InstructionBufferDepth),
    .axi_ar_t       (axi_ar_t),
    .axi_r_t        (axi_r_t),
    .BufferUsesMacro(BufferUsesMacro),
    .MemImplKey     (MemImplKey),
    .ram_impl_inp_t (ram_impl_inp_t),
    .ram_impl_oup_t (ram_impl_oup_t)
  ) u_aic_cd_axi_read (
    .i_clk,
    .i_rst_n,
    .o_busy             (o_axi_read_busy),
    .o_num_data_buffered(/* open */),
    .i_request_ar       (request_ar),
    .i_request_ar_valid (request_ar_valid),
    .o_request_ar_ready (request_ar_ready),
    .o_axi_m_ar,
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    .i_axi_m_r,
    .i_axi_m_r_valid,
    .o_axi_m_r_ready,
    .o_response_r       (response_r),
    .o_response_r_valid (response_r_valid),
    .i_response_r_ready (response_r_ready),
    .i_ram_impl,
    .o_ram_impl
  );

  ///////////////////////////////////////
  // Validate the fetched Instructions //
  ///////////////////////////////////////
  aic_cd_instruction_validate #(
    .NumDestinations     (NumDestinations),
    .NumPatchModeEntries (NumPatchModeEntries),
    .NumPatchTableEntries(NumPatchTableEntries),
    .NumLocalTokens      (NumLocalTokens),
    .NumGlobalTokens     (NumGlobalTokens),
    .axi_r_t             (axi_r_t)
  ) u_aic_cd_instrcution_validate (
    .i_clk,
    .i_rst_n,
    .i_metadata_task_list_length (metadata_task_list_length),
    .i_metadata_control_offset   (metadata_control_offset),
    .i_metadata_valid            (metadata_valid),
    .o_metadata_ready            (metadata_ready),
    .i_response_r                (response_r),
    .i_response_r_valid          (response_r_valid),
    .o_response_r_ready          (response_r_ready),
    .o_instruction,
    .o_instruction_control_offset,
    .o_instruction_last,
    .o_instruction_valid,
    .i_instruction_ready,
    .o_busy                      (o_validation_busy),
    .o_instruction_index,
    .o_instruction_emitted       (/* not used */),
    .o_instruction_dropped       (/* not used */),
    .i_drop_instructions,
    .o_validation_errors         (o_error_instruction_validation)
  );
endmodule
