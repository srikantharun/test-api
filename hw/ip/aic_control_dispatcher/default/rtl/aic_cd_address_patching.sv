// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// This unit provides address patching capabilities for commands.
///
/// !!! tip "Functional Usage"
///
///     Here we describe the hardware of the address patching. The functional usage is explained in
///     more detail in it's [own chapter](../../address_patching.md).
///
/// The address patching unit must take in a copy command to open up the datapath.  It keeps track
/// of the copied data via a counter which counts the word index to be copied.  As long as the unit
/// is busy by working on a copy command, the datapath is free to forward data.  The word index
/// keeps the copy command aligned to the data being copied.  The overal structure is the following:
///
/// ![AIC_CD_ADDRESS_PATCHING: Block Diagram](figures/aic_cd_address_patching.drawio.svg)
///
///
/// ## Finite State Machine
///
/// The FSM govens the control of the unit.  It is sensitive to *transactions* of the copied data.
/// It cycles though the different states to prime the combinational logic to apply the address patching.
/// `IDLE` waits for a new copy command to arrive and loads the respective coutner to keep track on the
/// word index that flows through the unit. `APPLY_*` states get primed if the counter reaches the word index
/// that is configured in the `csr.patch_mode` and matches the one that is given by the command field `patch_field`.
/// The `BYPASS` state handles copied programs which do not need any patching, data is simply forwarded. The FSM
/// has the following structure:
///
///
/// ```mermaid
/// stateDiagram-v2
///     IDLE
///     APPLY_0
///     APPLY_1
///     BYPASS
///
///     [*] --> IDLE
///     IDLE --> APPLY_0
///     IDLE --> BYPASS
///     APPLY_0 --> APPLY_1
///     APPLY_0 --> BYPASS
///     APPLY_0 --> IDLE
///     APPLY_1 --> BYPASS
///     APPLY_1 --> APPLY_0
///     APPLY_1 --> IDLE
///     BYPASS --> APPLY_0
///     BYPASS --> IDLE
/// ```
///
/// !!! note "Patch Mode Configuration"
///
///     Due to the FSM structure the `Patch Mode` has some restrictions in how they can be configured.
///
///     - If in ehe instruction field of patch mode that equals `0`, there will be no pathcing applied
///       as it does not amtch any patch_mode csr.
///     - The respective patch mode CSR fields of word_index and addr_width mus both be a value \
///       different to 0 to have a patch mode applied.
///         - Word index `0` matches the header, which can not be pached.
///         - Address Width `0` equates to a non existing address.
///     - The `patch 0` word index must be strictly smaller tahtn the one from `patch 1`.
///         - To apply only one patch set `patch 1` to `0`.
///
///
module aic_cd_address_patching #(
  /// The address width
  parameter int unsigned AddrWidth = 0,
  /// The data width of the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  localparam type data_t = logic[DataWidth-1:0],
  /// Number of patch mode entries
  parameter int unsigned NumPatchModeEntries  = aic_cd_csr_reg_pkg::NUM_PATCH_MODE_ENTRIES,
  /// Number of patch table entries
  parameter int unsigned NumPatchTableEntries = aic_cd_csr_reg_pkg::NUM_PATCH_TABLE_ENTRIES,
  /// The type describing the patch mode entries
  parameter type patch_mode_entry_t = aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_patch_mode_mreg_t,
  /// The type describing the patch table entries
  parameter type patch_table_entry_t = aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_patch_table_mreg_t,
  /// Number of pipeline stages to be inserted (minimum 1)
  parameter int unsigned NumPipelineStages = 1
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ////////////
  // Config //
  ////////////
  /// The patch mode entries
  input patch_mode_entry_t  [NumPatchModeEntries -1:0] i_patch_mode,
  /// The patch table entries
  input patch_table_entry_t [NumPatchTableEntries-1:0] i_patch_table,

  //////////////
  // Commands //
  //////////////
  /// The command what and how to patch
  input aic_cd_pkg::copy_command_t i_copy_command,
  /// The copy comand is valid
  input logic                      i_copy_command_valid,
  /// We are ready for the patch command
  output logic                     o_copy_command_ready,

  ///////////////////////
  // Input Data Stream //
  ///////////////////////
  /// The input data that needs patching
  input  data_t              i_data,
  /// Axi response type
  input  axi_pkg::axi_resp_e i_resp,
  /// The input stream is valid
  input  logic               i_data_valid,
  /// We are ready for the input stream
  output logic               o_data_ready,

  ////////////////////////
  // Output Data Stream //
  ////////////////////////
  /// The patched output data
  output data_t o_data,
  /// The patched data is valid
  output logic  o_data_valid,
  /// The downstream is ready
  input  logic  i_data_ready,

  ///////////////////////
  // Status and Errors //
  ///////////////////////
  /// The unit is busy
  output logic                               o_busy,
  /// The write response returnd a SLVERR
  output logic                               o_resp_slverr,
  /// The write response returnd a DECERR
  output logic                               o_resp_decerr,
  /// The instruction index the error occured
  output aic_cd_pkg::task_list_word_length_t o_instruction_index
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  if (DataWidth == 0) $fatal(1, "Parameter: 'DataWidth' must not be 0;");
  if (DataWidth % 8 != 0) $fatal(1, "Parameter: 'DataWidth (%d)' bust be divisable by 8;", DataWidth);
  if (DataWidth < unsigned'($bits(i_patch_mode[0].addr_width_0.q)))
      $fatal(1, "Parameter: 'DataWidth (%d)' can not represent 'patch_mode.addr_width (%d)';",
      DataWidth, $bits(i_patch_mode[0].addr_width_0.q));

  localparam int unsigned DataNumBytes = DataWidth / 8;

  typedef enum logic [1:0] {
    IDLE,
    APPLY_0,
    APPLY_1,
    BYPASS
  } state_e;
  state_e state_q, state_d;

  typedef logic [AddrWidth-1:0] address_t;

  /////////////////////////////////////////////////////
  // Keep command and Count the words to be expected //
  /////////////////////////////////////////////////////
  aic_cd_pkg::copy_command_t copy_command_q;
  logic                      copy_command_load;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)               copy_command_q <= aic_cd_pkg::copy_command_t'(0);
    else if (copy_command_load) copy_command_q <= i_copy_command;
  end

  aic_cd_pkg::copy_num_words_t word_index_q;
  logic                        word_transaction;

  cc_cnt_delta #(
    .Width         (aic_cd_pkg::CopyMaxNumWordsLength),
    .StickyOverflow(1'b0)
  ) u_word_counter (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (word_transaction),
    .i_cnt_down(1'b0),
    .i_delta   (aic_cd_pkg::copy_num_words_t'(1)),
    .o_q       (word_index_q),
    .i_d       (aic_cd_pkg::copy_num_words_t'(0)),
    .i_d_load  (copy_command_load),
    .o_overflow(/* not used */)
  );

  logic at_word_index_last;
  logic at_word_index_patch;
  logic skip_patch;

  always_comb at_word_index_last = ((word_index_q + aic_cd_pkg::copy_num_words_t'(1)) >= aic_cd_pkg::copy_num_words_t'(copy_command_q.num_words));
  always_comb begin : proc_patch_flags
    at_word_index_patch    = 1'b0;
    skip_patch             = 1'b0;
    unique case (state_q)
      APPLY_0: begin
        if (|copy_command_q.patch_mode) at_word_index_patch =
            (word_index_q == aic_cd_pkg::copy_num_words_t'(i_patch_mode[copy_command_q.patch_mode-1].word_index_0.q));
        else skip_patch = ~at_word_index_last;
      end
      APPLY_1: begin
        if (|copy_command_q.patch_mode) at_word_index_patch =
            (word_index_q == aic_cd_pkg::copy_num_words_t'(i_patch_mode[copy_command_q.patch_mode-1].word_index_1.q));
        else skip_patch = ~at_word_index_last;
      end
      default: /* use defaults */;
    endcase
  end

  ////////////////
  // AXI Errors //
  ////////////////

  always_comb o_resp_slverr       = i_data_valid & (i_resp == axi_pkg::RespSlvErr);
  always_comb o_resp_decerr       = i_data_valid & (i_resp == axi_pkg::RespDecErr);
  always_comb o_instruction_index = copy_command_q.instruction_index;

  /////////////////
  // Control FSM //
  /////////////////

  logic disconnect_data;

  always_comb begin : proc_control_fsm
    state_d              = state_q;
    copy_command_load    = 1'b0;
    o_copy_command_ready = 1'b0;
    disconnect_data      = 1'b0;

    unique case (state_q)
      IDLE: begin
        disconnect_data = 1'b1;
        o_copy_command_ready = 1'b1;
        if (i_copy_command_valid) begin
          copy_command_load = 1'b1;
          if (i_copy_command.opcode == aic_cd_pkg::OpcodeCommand) state_d = APPLY_0;
          else                                                    state_d = BYPASS;
        end
      end
      APPLY_0: begin
        if (word_transaction) begin
          if (skip_patch) begin
            state_d = APPLY_1;
          end else if (at_word_index_last) begin
            o_copy_command_ready = 1'b1;
            if (i_copy_command_valid) begin
              copy_command_load = 1'b1;
              if (i_copy_command.opcode == aic_cd_pkg::OpcodeCommand) state_d = APPLY_0;
              else                                                    state_d = BYPASS;
            end else begin
              state_d = IDLE;
            end
          end else if (at_word_index_patch) begin
            state_d = APPLY_1;
          end
        end
      end
      APPLY_1,
      BYPASS: begin
        if (at_word_index_last && word_transaction) begin
          o_copy_command_ready = 1'b1;
          if (i_copy_command_valid) begin
            copy_command_load = 1'b1;
            if (i_copy_command.opcode == aic_cd_pkg::OpcodeCommand) state_d = APPLY_0;
          end else begin
            state_d = IDLE;
          end
        end
      end
      default: /* use defaults */;
    endcase
  end

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) state_q <= IDLE;
    else          state_q <= state_d;
  end

  data_t internal_data;
  logic  internal_data_valid;
  logic  internal_data_ready;
  cc_stream_disconnect #(
    .data_t(data_t)
  ) u_disconnect_input (
    .i_disconnect (disconnect_data),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(word_transaction),
    .i_data,
    .i_valid      (i_data_valid),
    .o_ready      (o_data_ready),
    .o_data       (internal_data),
    .o_valid      (internal_data_valid),
    .i_ready      (internal_data_ready)
  );

  //////////////////////////
  // Perform the Patching //
  //////////////////////////
  localparam int unsigned ADDRESS_WIDTH_WIDTH = 4;
  typedef logic [ADDRESS_WIDTH_WIDTH-1:0] address_width_t;
  if (ADDRESS_WIDTH_WIDTH != unsigned'($bits(i_patch_mode[0].addr_width_0.q)))
      $fatal(1, "Parameter: 'ADDRESS_WIDTH_WIDTH (%d)' must match CSR 'PATACH_MODE_*.ADDR_WIDTH_* (%d)';",
      ADDRESS_WIDTH_WIDTH, $bits(i_patch_mode[0].addr_width_0.q));

  address_width_t address_width;
  always_comb begin
    unique case (state_q)
      APPLY_0: address_width = at_word_index_patch ? address_width_t'(i_patch_mode[copy_command_q.patch_mode-1].addr_width_0.q) : address_width_t'(0);
      APPLY_1: address_width = at_word_index_patch ? address_width_t'(i_patch_mode[copy_command_q.patch_mode-1].addr_width_1.q) : address_width_t'(0);
      default: address_width = address_width_t'(0);
    endcase
  end

  // Depending on parameterization either the data width or the CSR determine the range the patching is done.
  localparam int unsigned RangeDataBytes = (DataNumBytes < 32'd2**ADDRESS_WIDTH_WIDTH) ? DataNumBytes : 32'd2**ADDRESS_WIDTH_WIDTH;

  data_t extracted_address;
  always_comb begin : proc_extracted_address
    extracted_address = data_t'(0);
    for (int unsigned byte_index = 0; byte_index < RangeDataBytes; byte_index++) begin
      if (at_word_index_patch && (byte_index < address_width)) begin
        extracted_address[byte_index*8+:8] = internal_data[byte_index*8+:8];
      end
    end
  end

  address_t selected_patch_address;
  always_comb begin : proc_selected_patch_address
    unique case (state_q)
      APPLY_0: selected_patch_address = at_word_index_patch ? address_t'(i_patch_table[copy_command_q.patch_id_0].q) : address_t'(0);
      APPLY_1: selected_patch_address = at_word_index_patch ? address_t'(i_patch_table[copy_command_q.patch_id_1].q) : address_t'(0);
      default: selected_patch_address = address_t'(0);
    endcase
  end

  data_t      patched_address;
  always_comb patched_address = extracted_address + data_t'(selected_patch_address);

  data_t patched_data;
  always_comb begin : proc_patched_data
    patched_data = internal_data;
    for (int unsigned byte_index = 0; byte_index < RangeDataBytes; byte_index++) begin
      if (at_word_index_patch && (byte_index < address_width)) begin
        patched_data[byte_index*8+:8] = patched_address[byte_index*8+:8];
      end
    end
  end

  /////////////////////////////////////////////////////////////
  // Output Pipeline to break path after muxing and addition //
  /////////////////////////////////////////////////////////////
  data_t                         pipeline_q[NumPipelineStages+1];
  logic  [NumPipelineStages-1:0] pipeline_load;
  logic  [NumPipelineStages-1:0] pipeline_state;

  always_comb pipeline_q[0] = patched_data;

  cc_stream_pipe_load #(
    .NumStages(NumPipelineStages)
  ) u_cc_stream_pipe_load (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0), // Not used
    .i_valid(internal_data_valid),
    .o_ready(internal_data_ready),
    .o_load (pipeline_load),
    .o_state(pipeline_state),
    .o_valid(o_data_valid),
    .i_ready(i_data_ready)
  );

  for (genvar pipe_index = 0; unsigned'(pipe_index) < NumPipelineStages; pipe_index++) begin : gen_stage
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)                       pipeline_q[pipe_index+1] <= data_t'(0);
      else if (pipeline_load[pipe_index]) pipeline_q[pipe_index+1] <= pipeline_q[pipe_index];
    end
  end

  always_comb o_data = pipeline_q[NumPipelineStages];

  ////////////
  // Status //
  ////////////
  always_comb o_busy =
    (state_q != IDLE)
  | (|pipeline_state);
endmodule
