// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// This unit is responsible for copying commands and programs, keep track of downstream outstanding commands as well as address patching.
///
/// !!! warning "Unaligned Data: Not Supported"
///
///     The Copy Unit currently does not support data unaligned copy operations. This means the source and target address
///     must match in the LSBs of their addresses!
///
///     If they do not match the offending instruction will be dropped before the command is sent further in the pipeline.
///
/// The `Copy Unit` is responsible for executing [`cmd`](../../instructions.md#copy-instruction-cmd) and
/// [`prg`](../../instructions.md#copy-instruction-prg) instructions.  The instructions are translated into `copy commands`
/// by the [Execution Unit](../execute.md) which is responsible for filling in the correct values for the different fiels.
/// The command contains everything that is needed to perform the reading and writing of the copied data.  The command
/// then gets sent to different sub-units, each of which is responsible of performing a different sub-task.  The
/// synchronization is purely handled via `AXI-style` `valid/ready` handshaking.  The thoughput can be optimized by
/// carefully tweaking the depths of the respective copy command buffers.
///
/// There exist 4 main sub-units each of which perform a different action.  Connecting them up in this way results in the
/// emerging copy functionality.
///
/// - [Read Request Unit](read_request.md): Requests data to be copied.
/// - [Address Patching Unit](address_patching.md): Takes requested data and can perform [patching of addresses](../../address_patching.md).
/// - [Fill Counters](fill_counters.md): Pessimisticly estimate the fill status of destination command FIFOs.  Gates commands towards the write unit if needed.
/// - [Write Request Unit](write_request.md): Write the address patched data to the destiantion.
///
/// The structure of the copy unit is as follows:
///
/// ![AIC_CD_COPY_UNIT: Block Diagram](figures/aic_cd_copy_unit.drawio.svg)
///
/// !!! note "Fill Counters"
///
///     The [Fill Counters](fill_counters.md) act as the gate keeper for copy instructions reaching the write request unit.
///     Which means even if the downstream command FIFO is full, the to be copied data already can be read in and patched.
///
///
/// ## Copy Command
///
/// ::: hw/ip/aic_control_dispatcher/default/rtl/pkg/aic_cd_pkg.sv:aic_cd_pkg.copy_command_t
///
///
/// ## Error Behaviour
///
/// As the `copy instructions` are distributed to the different sub-units any command that gets distributed is considered
/// in flight and **will finish** even if there are errors encountered.  The unit will do it's best to report the first failing instruction.
/// For this there exists a priority multiplexer which will forward the `instruction index` that triggered the error.  We can only report the
/// error for the units which know the respective instruction which triggered the error.  The *pop-error* from the `Fill Coutners` can *not*
/// report the instruction that triggered it, as this error happens on a counter which is considered empty.  So no instruction associated with it.
/// The priority is chosen in a way that units lower down the stream has priority:
///
/// 1. `AXI Write Response Error`: The last unit that does something with a copy command.
/// 2. `AXI Read Response Error`: Intermediate unit.
/// 3. `Data Unaligned Error`: This is at the control entry.
///
/// !!! waring "Copy Errors"
///
///     Errors in the copy unit will have the instruction finish executing, even if this might lead to corruption of
///     data being copied. Currently there is no mechanism to interrupt a `copy command` which has started.  We rely
///     on reporting the error to the best of our ability by providing where it happened and which `instruction index`
///     caused it.  The [Validation Unit](../instruction_fetch/validate.md) is then responsible of dropping the remainder
///     of the task list.
///
///
/// ::: hw/ip/aic_control_dispatcher/default/rtl/pkg/aic_cd_pkg.sv:aic_cd_pkg.copy_errors_t
///
module aic_cd_copy_unit #(
  /// The number of destinations the unit interacts with
  parameter int unsigned NumDestinations = 17,
  /// The number of Patch Mode entries
  parameter int unsigned NumPatchModeEntries = 8,
  /// The number of Patch Table entries
  parameter int unsigned NumPatchTableEntries = 16,
  /// The Axi ID width of the AXI channel
  parameter int unsigned AxiIdWidth = aic_cd_defaults_pkg::AXI_M_ID_WIDTH,
  /// The Concrete AXI ID to use
  parameter logic [AxiIdWidth-1:0] AxiIdForCopy = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(0),
  /// The Address width of the AXI channel
  parameter int unsigned AxiAddrWidth = aic_cd_defaults_pkg::AXI_M_ADDR_WIDTH,
  /// The Data width of the AXI channel
  parameter int unsigned AxiDataWidth = aic_cd_defaults_pkg::AXI_M_DATA_WIDTH,
  /// The depth of the instruction buffer.
  parameter int unsigned CopyBufferDepth = 32,
  /// The depth of the Fill Counter Fifos
  parameter int unsigned FillCounterDepth = 8,

  /// The type describing the overall parameterization of the command block FIFOs
  parameter type dst_cmdblock_params_t = aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_dst_cmdblock_params_mreg_t,
  /// The type describing the patch mode entries
  parameter type patch_mode_entry_t = aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_patch_mode_mreg_t,
  /// The type describing the patch table entries
  parameter type patch_table_entry_t = aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_patch_table_mreg_t,

  /// AW Channel Type
  parameter type axi_aw_t = aic_cd_defaults_pkg::axi_m_aw_t,
  ///  W Channel Type
  parameter type axi_w_t  = aic_cd_defaults_pkg::axi_m_w_t,
  ///  B Channel Type
  parameter type axi_b_t  = aic_cd_defaults_pkg::axi_m_b_t,
  /// The AXI AR channel type
  parameter type axi_ar_t = aic_cd_defaults_pkg::axi_m_ar_t,
  /// The AXI R channel type
  parameter type axi_r_t  = aic_cd_defaults_pkg::axi_m_r_t,
  /// Use a memory for the buffer
  parameter bit BufferUsesMacro = 1'b1,
  /// Memory Implementation Key for the copy buffer
  parameter MemImplKey = "default",
  /// Sideband input signal type to tc_sram
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  //////////////////
  // Copy Request //
  //////////////////
  /// The copy command
  input  aic_cd_pkg::copy_command_t i_copy_command,
  /// The copy command is valid
  input  logic                      i_copy_command_valid,
  /// Dowstream consumes copy command
  output logic                      o_copy_command_ready,

  //////////////////////
  // AXI Manager port //
  //////////////////////
  output axi_aw_t o_axi_m_aw,
  output logic    o_axi_m_aw_valid,
  input  logic    i_axi_m_aw_ready,
  output axi_w_t  o_axi_m_w,
  output logic    o_axi_m_w_valid,
  input  logic    i_axi_m_w_ready,
  input  axi_b_t  i_axi_m_b,
  input  logic    i_axi_m_b_valid,
  output logic    o_axi_m_b_ready,
  output axi_ar_t o_axi_m_ar,
  output logic    o_axi_m_ar_valid,
  input  logic    i_axi_m_ar_ready,
  input  axi_r_t  i_axi_m_r,
  input  logic    i_axi_m_r_valid,
  output logic    o_axi_m_r_ready,

  /////////////////////////////
  // Destination Done Pulses //
  /////////////////////////////
  // Each destination must raise a done pulse
  input  logic [NumDestinations-1:0] i_destination_done,

  ////////////////////////////////////
  // Stattic Configuration from CSR //
  ////////////////////////////////////
  /// The CSRs containing the parameterization of the commandblock
  ///
  /// These must be stable during operation
  input  dst_cmdblock_params_t [NumDestinations-1:0] i_destination_cmdblock_params,
  /// The patch mode entries
  input  patch_mode_entry_t  [NumPatchModeEntries -1:0] i_patch_mode,
  /// The patch table entries
  input  patch_table_entry_t [NumPatchTableEntries-1:0] i_patch_table,

  ////////////
  // Errors //
  ////////////
  /// Erros detected in this unit
  output aic_cd_pkg::copy_errors_t           o_errors,
  /// The instruction index the error occured
  output aic_cd_pkg::task_list_word_length_t o_instruction_index,

  ////////////
  // Status //
  ////////////
  /// The read request is busy / is outstanding
  output logic                             o_read_request_busy,
  /// The read manager is busy
  output logic                             o_axi_read_busy,
  /// The address patching is busy
  output logic                             o_address_patching_busy,
  /// The fill counters are busy
  output logic                             o_fill_counters_busy,
  /// The write request is busy / is outstanding
  output logic                             o_write_request_busy,
  /// The unit is actively stalling because the respective counter said so
  output logic                             o_command_stalled,
  /// The respective fill counter is at capacity
  output logic                             o_must_be_stalled[NumDestinations],
  /// The respective fill counter value
  output aic_cd_pkg::command_byte_length_t o_fill_count[NumDestinations],

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
  typedef logic [AxiDataWidth-1:0] copy_data_t;

  ///////////////////////////////
  // Validate the Copy Command //
  ///////////////////////////////
  logic copy_validate_valid;
  logic copy_validate_ready;

  // Drop if the request addresses are not data aligned, then we would need to shift the data
  // On the byte lanes, which is curerntly not supported. Drop the command in this case!
  logic       drop_copy_command;
  always_comb drop_copy_command =
         i_copy_command.addr_source[0+:aic_cd_pkg::CopyDataNumBytesWidth]
      != i_copy_command.addr_destination[0+:aic_cd_pkg::CopyDataNumBytesWidth];

  cc_stream_filter u_validation_filter (
    .i_drop   (drop_copy_command),
    .o_dropped(o_errors.copy_data_misaligned),
    .i_valid  (i_copy_command_valid),
    .o_ready  (o_copy_command_ready),
    .o_valid  (copy_validate_valid),
    .i_ready  (copy_validate_ready)
  );

  //////////////////////////////////////////////////////////
  // Fork the Copy request to all units in the Copy Chain //
  //////////////////////////////////////////////////////////
  localparam int unsigned NUM_SUB_UNITS = 3;
  typedef enum logic[cc_math_pkg::index_width(NUM_SUB_UNITS)-1:0] {
    AXI_READ_UNIT,
    ADDR_PATCH_UNIT,
    AXI_WRITE_UNIT
  } sub_unit_index_e;

  logic [NUM_SUB_UNITS-1:0] copy_command_valid;
  logic [NUM_SUB_UNITS-1:0] copy_command_ready;

  cc_stream_fork #(
    .NumStreams(NUM_SUB_UNITS)
  ) u_copy_request_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select({NUM_SUB_UNITS{1'b1}}),
    .i_valid (copy_validate_valid),
    .o_ready (copy_validate_ready),
    .o_valid (copy_command_valid),
    .i_ready (copy_command_ready)
  );

  ///////////////
  // Copy Read //
  ///////////////
  axi_ar_t request_ar;
  logic    request_ar_valid;
  logic    request_ar_ready;

  aic_cd_copy_read_request #(
    .AxiIdWidth  (AxiIdWidth),
    .AxiIdForCopy(AxiIdForCopy),
    .AxiAddrWidth(AxiAddrWidth),
    .axi_ar_t    (axi_ar_t)
  ) u_aic_cd_copy_read_request (
    .i_clk,
    .i_rst_n,
    .o_busy              (o_read_request_busy),
    .i_copy_command,
    .i_copy_command_valid(copy_command_valid[AXI_READ_UNIT]),
    .o_copy_command_ready(copy_command_ready[AXI_READ_UNIT]),
    .o_request_ar        (request_ar),
    .o_request_ar_valid  (request_ar_valid),
    .i_request_ar_ready  (request_ar_ready)
  );

  /////////////////////////////////////////////////////
  // Fetch the Commands and Programs from the Memory //
  /////////////////////////////////////////////////////
  axi_r_t response_r;
  logic   response_r_valid;
  logic   response_r_ready;

  aic_cd_axi_read #(
    .AxiAddrWidth   (AxiAddrWidth),
    .ReadBufferDepth(CopyBufferDepth),
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

  //////////////////////
  // Address Patching //
  //////////////////////
  aic_cd_pkg::copy_command_t patch_command;
  logic                      patch_command_valid;
  logic                      patch_command_ready;

  copy_data_t                patched_data;
  logic                      patched_data_valid;
  logic                      patched_data_ready;

  aic_cd_pkg::task_list_word_length_t read_instruction_index;

  cc_stream_spill_reg #(
    .data_t(aic_cd_pkg::copy_command_t)
  ) u_buffer_address_patch (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_copy_command),
    .i_valid(copy_command_valid[ADDR_PATCH_UNIT]),
    .o_ready(copy_command_ready[ADDR_PATCH_UNIT]),
    .o_data (patch_command),
    .o_valid(patch_command_valid),
    .i_ready(patch_command_ready)
  );

  aic_cd_address_patching #(
    .AddrWidth           (AxiAddrWidth),
    .DataWidth           (AxiDataWidth),
    .NumPatchModeEntries (NumPatchModeEntries),
    .NumPatchTableEntries(NumPatchTableEntries),
    .patch_mode_entry_t  (patch_mode_entry_t),
    .patch_table_entry_t (patch_table_entry_t),
    .NumPipelineStages   (1)
  ) u_aic_cd_address_patching (
    .i_clk,
    .i_rst_n,
    .i_patch_mode,
    .i_patch_table,
    .i_copy_command      (patch_command),
    .i_copy_command_valid(patch_command_valid),
    .o_copy_command_ready(patch_command_ready),
    .i_data              (response_r.data),
    .i_resp              (axi_pkg::axi_resp_e'(response_r.resp)),
    .i_data_valid        (response_r_valid),
    .o_data_ready        (response_r_ready),
    .o_data              (patched_data),
    .o_data_valid        (patched_data_valid),
    .i_data_ready        (patched_data_ready),
    .o_busy              (o_address_patching_busy),
    .o_resp_slverr       (o_errors.axi_read_response_slverr),
    .o_resp_decerr       (o_errors.axi_read_response_decerr),
    .o_instruction_index (read_instruction_index)
  );

  //////////////////////////////////
  // Fill Counters gate the write //
  //////////////////////////////////
  aic_cd_pkg::copy_command_t copy_command_write;
  logic                      copy_command_write_valid;
  logic                      copy_command_write_ready;

  logic [NumDestinations-1:0] error_fill_counter_done_pop;
  logic [NumDestinations-1:0] error_fill_counter_overflow;

  aic_cd_fill_counters #(
    .NumDestinations      (NumDestinations),
    .FifoDepth            (FillCounterDepth),
    .dst_cmdblock_params_t(dst_cmdblock_params_t)
  ) u_aic_cd_fill_counters (
    .i_clk,
    .i_rst_n,
    .i_copy_command,
    .i_copy_command_valid         (copy_command_valid[AXI_WRITE_UNIT]),
    .o_copy_command_ready         (copy_command_ready[AXI_WRITE_UNIT]),
    .o_copy_command               (copy_command_write),
    .o_copy_command_valid         (copy_command_write_valid),
    .i_copy_command_ready         (copy_command_write_ready),
    .i_destination_cmdblock_params,
    .i_destination_done,
    .o_busy                       (o_fill_counters_busy),
    .o_command_stalled,
    .o_must_be_stalled,
    .o_fill_count,
    .o_error_done_pop             (error_fill_counter_done_pop),
    .o_error_overflow             (error_fill_counter_overflow)
  );

  assign o_errors.fill_counter_done_pop = |error_fill_counter_done_pop;
  assign o_errors.fill_counter_overflow = |error_fill_counter_overflow;

  /////////////////////////////////////////
  // Write the commands back into memory //
  /////////////////////////////////////////
  aic_cd_pkg::task_list_word_length_t write_instruction_index;

  aic_cd_copy_write_request #(
    .AxiIdWidth  (AxiIdWidth),
    .AxiIdForCopy(AxiIdForCopy),
    .AxiAddrWidth(AxiAddrWidth),
    .AxiDataWidth(AxiDataWidth),
    .axi_aw_t    (axi_aw_t),
    .axi_w_t     (axi_w_t),
    .axi_b_t     (axi_b_t)
  ) u_aic_cd_copy_write_request (
    .i_clk,
    .i_rst_n,
    .o_busy              (o_write_request_busy),
    .o_resp_slverr       (o_errors.axi_write_response_slverr),
    .o_resp_decerr       (o_errors.axi_write_response_decerr),
    .o_instruction_index (write_instruction_index),
    .i_copy_command      (copy_command_write),
    .i_copy_command_valid(copy_command_write_valid),
    .o_copy_command_ready(copy_command_write_ready),
    .i_patched_data      (patched_data),
    .i_patched_data_valid(patched_data_valid),
    .o_patched_data_ready(patched_data_ready),
    .o_axi_m_aw,
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    .o_axi_m_w,
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    .i_axi_m_b,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready
  );

  ///////////////////////////
  // Propagate Error Index //
  ///////////////////////////

  // Lower down the chain has priority
  always_comb begin
    if (o_errors.axi_write_response_slverr || o_errors.axi_write_response_decerr)
      o_instruction_index = write_instruction_index;
    else if (o_errors.axi_read_response_slverr || o_errors.axi_read_response_decerr)
      o_instruction_index = read_instruction_index;
    else if (o_errors.copy_data_misaligned)
      o_instruction_index = i_copy_command.instruction_index;
    else
      o_instruction_index = aic_cd_pkg::task_list_word_length_t'(0);
  end
endmodule
