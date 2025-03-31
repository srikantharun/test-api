// (C) Copyright 2022 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owners:
//   - Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//   - Stefan Mach <stefan.mach@axelera.ai>

/// Use a unified loop command to generate a datapath command stream.
///
module aic_dp_cmd_gen #(
  /// AXI4 Identification Width
  parameter int unsigned AxiIdWidth   = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH,
  /// AXI4 Address Width
  parameter int unsigned AxiAddrWidth = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH,
  /// AXI4 Data Width
  parameter int unsigned AxiDataWidth = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH,
  /// AXI4 Strobe Width
  localparam int unsigned AxiStrbWidth = AxiDataWidth / 8,
  /// AXI Endpoint Address Start
  ///
  /// Used for AXI address realignmnt
  parameter logic [AxiAddrWidth-1:0] AxiEndpointStart = AxiAddrWidth'(0),
  /// AXI Endpoint Address Size
  ///
  /// Used for AXI address realignbnt
  parameter logic [AxiAddrWidth-1:0] AxiEndpointSize  = AxiAddrWidth'(0),

  /// Maximum Number of outstanding commands that can be in flight towards the datapath
  parameter int unsigned MaxOutstanding = 3,

  /// Data type for the datapath command custom to the datapath
  parameter type dp_command_t = aic_dp_cmd_gen_pkg::dummy_dp_command_t,

  /// Memory depth for the datapath command storage
  parameter int unsigned DpCommandMemoryDepth = 0,
  /// Add an additional pipeline stage in the datapath command memory
  parameter bit DpCommandMemoryShield = 1'b0,

  /// Change the data alignment of the AXI bus in relation to the memory.
  ///
  /// Changing this value to have multiple rows inside a DW will result a different memory configuration.
  /// Example:
  ///
  /// - `.AxiDataWidth(64)`
  /// - `$bits(dp_command_t) == 30 `
  /// - `.DpCommandMemoryDepth(4)`
  /// - `.DpCommandMemoryDataAlign(32)`
  ///
  /// --> will for example result in a memory of 2 deep and 60 wide
  parameter int unsigned DpCommandMemoryDataAlign = AxiDataWidth,

  /// Use a technology specifc memory macro for the datapath command storage
  parameter bit UseMemoryMacro = 1'b1,

  /// Memory Implementation Key (only used if `UseMemoryMacro == 1`)
  parameter MemImplKey = "HS_RVT",
  /// Sideband input signal type to tc_sram  (only used if `UseMemoryMacro == 1`)
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram  (only used if `UseMemoryMacro == 1`)
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
)(
  /// Clock, positive edge triggered
  input wire  i_clk,
  /// Asynchronous reset, active low
  input wire  i_rst_n,
  /// Purge everything go back to idle
  input logic i_flush,
  /// Thest mode is active, enable all manual clock-gates
  input logic i_test_mode,

  /////////////////////////////
  // CMD Block Command Input //
  /////////////////////////////
  /// Command data from the command block
  input  aic_dp_cmd_gen_pkg::cmdb_cmd_t   i_cmdb_command,
  /// Command format from the command block
  input  aic_dp_cmd_gen_pkg::cmd_format_e i_cmdb_format,
  /// The config field from the command header
  input  aic_dp_cmd_gen_pkg::cmd_config_t i_cmdb_config,
  /// The command is valid flag
  input  logic                            i_cmdb_valid,
  /// The ready flag for the command
  output logic                            o_cmdb_ready,

  /// Pulse signal to the command block to indicate that a command is done
  ///
  /// One pulse per handshaked command
  output logic                            o_cmdb_done,

  ////////////////////////////////////////
  // AXI Subordinate Instruction Memory //
  ////////////////////////////////////////
  // Write Address Channel
  input  logic [  AxiIdWidth-1:0] i_axi_s_aw_id,
  input  logic [AxiAddrWidth-1:0] i_axi_s_aw_addr,
  input  axi_pkg::axi_len_t       i_axi_s_aw_len,
  input  axi_pkg::axi_size_t      i_axi_s_aw_size,
  input  axi_pkg::axi_burst_t     i_axi_s_aw_burst,
  input  logic                    i_axi_s_aw_valid,
  output logic                    o_axi_s_aw_ready,
  // Write Data Channel
  input  logic [AxiDataWidth-1:0] i_axi_s_w_data,
  input  logic [AxiStrbWidth-1:0] i_axi_s_w_strb,
  input  logic                    i_axi_s_w_last,
  input  logic                    i_axi_s_w_valid,
  output logic                    o_axi_s_w_ready,
  // Write Response Channel
  output logic [  AxiIdWidth-1:0] o_axi_s_b_id,
  output axi_pkg::axi_resp_t      o_axi_s_b_resp,
  output logic                    o_axi_s_b_valid,
  input  logic                    i_axi_s_b_ready,
  // Read Address Channel
  input  logic [  AxiIdWidth-1:0] i_axi_s_ar_id,
  input  logic [AxiAddrWidth-1:0] i_axi_s_ar_addr,
  input  axi_pkg::axi_len_t       i_axi_s_ar_len,
  input  axi_pkg::axi_size_t      i_axi_s_ar_size,
  input  axi_pkg::axi_burst_t     i_axi_s_ar_burst,
  input  logic                    i_axi_s_ar_valid,
  output logic                    o_axi_s_ar_ready,
  // Read Data Channel
  output logic [  AxiIdWidth-1:0] o_axi_s_r_id,
  output logic [AxiDataWidth-1:0] o_axi_s_r_data,
  output axi_pkg::axi_resp_t      o_axi_s_r_resp,
  output logic                    o_axi_s_r_last,
  output logic                    o_axi_s_r_valid,
  input  logic                    i_axi_s_r_ready,

  ////////////////////////////////////
  // Datapath Command Stream Output //
  ////////////////////////////////////
  /// Instruction data custom to the block using the command generator
  output dp_command_t                          o_dp_command_data,
  /// Command metadata stattic per command
  output aic_dp_cmd_gen_pkg::metadata_t        o_dp_command_metadata,
  /// Command iteration data specific to the datapath command
  output aic_dp_cmd_gen_pkg::loop_iterations_t o_dp_command_iterations,
  /// This is the last datapath command for this command
  output logic                                 o_dp_command_last,
  /// The datapath command is valid flag
  output logic                                 o_dp_command_valid,
  /// The ready flag for this datapath command
  input  logic                                 i_dp_command_ready,

  /// Pulse from the datapath indicating that all datapath commands have been executed
  ///
  /// One pulse per handshaked `o_dp_command_last`
  input  logic                                 i_dp_done,

  ///////////////////////////
  // Error and IRQ signals //
  ///////////////////////////
  /// Error conditions for the loops
  output aic_dp_cmd_gen_pkg::loop_errors_t o_errors,

  //////////////////////////////////////////////
  // Instruction memory SRAM sideband signals //
  //////////////////////////////////////////////
  /// Memory sideband input  signals, only used if `UseMacro == 1`
  input  ram_impl_inp_t i_ram_impl,
  /// Memory sideband output signals, only used if `UseMacro == 1`
  output ram_impl_oup_t o_ram_impl
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  if (AxiEndpointSize == AxiAddrWidth'(0)) $fatal(1, "Parameter: 'AxiEndpointSize' must be overwritten;");

  //////////////////////
  // Command Decoding //
  //////////////////////
  aic_dp_cmd_gen_pkg::loop_descriptor_t decode_descriptor;
  logic                                 decode_descriptor_valid;
  logic                                 decode_descriptor_ready;

  aic_dp_cmd_gen_pkg::metadata_t        decode_metadata;
  logic                                 decode_metadata_valid;
  logic                                 decode_metadata_ready;

  aic_dp_cmd_gen_decode #(
    .DpCommandMemoryDepth(DpCommandMemoryDepth),
    .MaxOutstanding        (MaxOutstanding)
  ) u_aic_dp_cmd_gen_decode (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_cmdb_command,
    .i_cmdb_format,
    .i_cmdb_config,
    .i_cmdb_valid,
    .o_cmdb_ready,
    .o_cmdb_done,
    .i_dp_done,
    .o_loop_descriptor      (decode_descriptor),
    .o_loop_descriptor_valid(decode_descriptor_valid),
    .i_loop_descriptor_ready(decode_descriptor_ready),
    .o_metadata             (decode_metadata),
    .o_metadata_valid       (decode_metadata_valid),
    .i_metadata_ready       (decode_metadata_ready),
    .o_errors
  );

  ////////////////////////////
  // Loop Descriptor Buffer //
  ////////////////////////////

  aic_dp_cmd_gen_pkg::loop_descriptor_t loop_descriptor;
  logic                                 loop_descriptor_valid;
  logic                                 loop_descriptor_ready;

  cc_stream_fifo #(
    .Depth      (3*MaxOutstanding),
    .data_t     (aic_dp_cmd_gen_pkg::loop_descriptor_t),
    .FallThrough(1'b0)
  ) u_cc_stream_fifo_loop_descriptor (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_data  (decode_descriptor),
    .i_valid (decode_descriptor_valid),
    .o_ready (decode_descriptor_ready),
    .o_data  (loop_descriptor),
    .o_valid (loop_descriptor_valid),
    .i_ready (loop_descriptor_ready),
    .o_usage (/* not used */), // ASO-UNUSED_OUTPUT : No onservability needed.
    .o_full  (/* not used */), // ASO-UNUSED_OUTPUT : No onservability needed.
    .o_empty (/* not used */)  // ASO-UNUSED_OUTPUT : No onservability needed.
  );

  aic_dp_cmd_gen_pkg::metadata_t loop_metadata;
  logic                          loop_metadata_valid;
  logic                          loop_metadata_ready;

  cc_stream_fifo #(
    .Depth      (MaxOutstanding),
    .data_t     (aic_dp_cmd_gen_pkg::metadata_t),
    .FallThrough(1'b0)
  ) u_cc_stream_fifo_extra_data (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_data  (decode_metadata),
    .i_valid (decode_metadata_valid),
    .o_ready (decode_metadata_ready),
    .o_data  (loop_metadata),
    .o_valid (loop_metadata_valid),
    .i_ready (loop_metadata_ready),
    .o_usage (/* not used */), // ASO-UNUSED_OUTPUT : No onservability needed.
    .o_full  (/* not used */), // ASO-UNUSED_OUTPUT : No onservability needed.
    .o_empty (/* not used */)  // ASO-UNUSED_OUTPUT : No onservability needed.
  );

  /////////////////////////////
  // Datapath LOOP Generator //
  /////////////////////////////
  aic_dp_cmd_gen_pkg::loop_pointer_t    address_pointer;
  aic_dp_cmd_gen_pkg::loop_iterations_t address_iterations;
  logic                                 address_last;
  logic                                 address_bypass;
  logic                                 address_valid;
  logic                                 address_ready;

  aic_dp_cmd_gen_loops #(
    .DpCommandMemoryDepth(DpCommandMemoryDepth)
  ) u_aic_dp_cmd_gen_loops (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_loop_descriptor      (loop_descriptor),
    .i_loop_descriptor_valid(loop_descriptor_valid),
    .o_loop_descriptor_ready(loop_descriptor_ready),
    .o_address_pointer      (address_pointer),
    .o_address_iterations   (address_iterations),
    .o_address_last         (address_last),
    .o_address_bypass       (address_bypass),
    .o_address_valid        (address_valid),
    .i_address_ready        (address_ready),
    .o_loop_errors          (/* not used */) // ASO-UNUSED_OUTPUT : Due to validation in decode commands are clean and do not have errors anymore.
  );

  ////////////////////////
  // Instruction Memory //
  ////////////////////////
  localparam int unsigned InstructionAddressWidth = cc_math_pkg::index_width(DpCommandMemoryDepth);
  typedef logic [InstructionAddressWidth-1:0] command_address_t;

  typedef struct packed {
    logic                                 last;
    logic                                 bypass;
    aic_dp_cmd_gen_pkg::loop_iterations_t iterations;
  } command_sideband_t;

  // Cast to specific length matching the memory
  command_address_t  command_address;
  command_sideband_t command_sideband;
  always_comb command_address = command_address_t'(address_pointer);


  always_comb command_sideband = '{
    last:       address_last,
    bypass:     address_bypass,
    iterations: address_iterations
  };

  // Inside signals (at instr mem instance)
  command_address_t  command_memory_address;
  logic              command_memory_address_valid;
  logic              command_memory_address_ready;

  dp_command_t       command_data;
  logic              command_valid;

  dp_command_t       dp_command_data;
  command_sideband_t dp_command_sideband;
  logic              dp_command_valid;
  logic              dp_command_ready;

  axe_ccl_stream_to_mem #(
    .BufferDepth(2),
    .req_data_t (command_address_t),
    .rsp_data_t (dp_command_t),
    .sideband_t (command_sideband_t)
  ) u_axe_ccl_stream_to_mem (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_req_data     (command_address),
    .i_req_sideband (command_sideband),
    .i_req_bypass   (command_sideband.bypass),
    .i_req_gen_rsp  (1'b1),
    .i_req_valid    (address_valid),
    .o_req_ready    (address_ready),
    .o_mem_req_data (command_memory_address),
    .o_mem_req_valid(command_memory_address_valid),
    .i_mem_req_ready(command_memory_address_ready),
    .i_mem_rsp_data (command_data),
    .i_mem_rsp_valid(command_valid),
    .o_rsp_data     (dp_command_data),
    .o_rsp_sideband (dp_command_sideband), // ASO-UNUSED_VARIABLE : dp_command_sideband.bypass from here on no longer needed.
    .o_rsp_valid    (dp_command_valid),
    .i_rsp_ready    (dp_command_ready)
  );


  // Address cap is the number of AXI words the mem must be able to save
  localparam int unsigned DpCommandMemoryWidth = $bits(command_data);

  // Address translation only if address space is misaligned
  logic [AxiAddrWidth-1:0] axi_s_aw_addr;
  logic [AxiAddrWidth-1:0] axi_s_ar_addr;

  if (AxiEndpointStart % AxiEndpointSize != 0) begin : gen_addr_translation
    always_comb axi_s_aw_addr = i_axi_s_aw_addr - AxiEndpointStart;
    always_comb axi_s_ar_addr = i_axi_s_ar_addr - AxiEndpointStart;
  end else begin : gen_addr_feedthrough
    always_comb axi_s_aw_addr = i_axi_s_aw_addr;
    always_comb axi_s_ar_addr = i_axi_s_ar_addr;
  end

  cmdblock_desc_mem #(
    .IDW           (AxiIdWidth),
    .AW            (AxiAddrWidth),
    .DW            (AxiDataWidth),
    .BW            (axi_pkg::AXI_LEN_WIDTH),
    .MEM_DEPTH     (DpCommandMemoryDepth),
    .MEM_WIDTH     (DpCommandMemoryWidth),
    .ARB_SCHEME    (aic_common_pkg::AIC_GEN_DESC_MEM_ARB_SCHEME),
    .OUTP_SHIELD   (DpCommandMemoryShield),
    .ADDR_CAP      (AxiEndpointSize),
    .DATA_ALIGN    (DpCommandMemoryDataAlign),
    .USE_MACRO     (UseMemoryMacro),
    .SRAM_IMPL_KEY (MemImplKey),
    .ram_impl_inp_t(ram_impl_inp_t),
    .ram_impl_oup_t(ram_impl_oup_t)
  ) u_cmdblock_desc_mem (
    .i_clk,
    .i_rst_n,
    .scan_mode         (i_test_mode),
    .awid              (i_axi_s_aw_id),
    .awaddr            (  axi_s_aw_addr),
    .awlen             (i_axi_s_aw_len),
    .awsize            (i_axi_s_aw_size),
    .awburst           (i_axi_s_aw_burst),
    .awvalid           (i_axi_s_aw_valid),
    .awready           (o_axi_s_aw_ready),
    .arid              (i_axi_s_ar_id),
    .araddr            (  axi_s_ar_addr),
    .arlen             (i_axi_s_ar_len),
    .arsize            (i_axi_s_ar_size),
    .arburst           (i_axi_s_ar_burst),
    .arvalid           (i_axi_s_ar_valid),
    .arready           (o_axi_s_ar_ready),
    .wdata             (i_axi_s_w_data),
    .wstrb             (i_axi_s_w_strb),
    .wlast             (i_axi_s_w_last),
    .wvalid            (i_axi_s_w_valid),
    .wready            (o_axi_s_w_ready),
    .rid               (o_axi_s_r_id),
    .rdata             (o_axi_s_r_data),
    .rresp             (o_axi_s_r_resp),
    .rlast             (o_axi_s_r_last),
    .rvalid            (o_axi_s_r_valid),
    .rready            (i_axi_s_r_ready),
    .bid               (o_axi_s_b_id),
    .bresp             (o_axi_s_b_resp),
    .bvalid            (o_axi_s_b_valid),
    .bready            (i_axi_s_b_ready),
    .rd_row_rvalid     (command_memory_address_valid),
    .rd_row_raddr      (command_memory_address),
    .rd_row_rready     (command_memory_address_ready),
    .rd_resp_vld       (command_valid),
    .rd_resp_data      (command_data),
    .i_sram_impl       (i_ram_impl),
    .o_sram_impl       (o_ram_impl)
  );

  /////////////////////////////
  // Datapath Output forming //
  /////////////////////////////

  // The extra data resides in a bypass FIFO. There should be extra delay though the loop genration
  // and the command memory that it arrives on the port on time. We pop it on the last flag.
  logic       metadata_connect;
  always_comb metadata_connect = dp_command_valid & dp_command_sideband.last;

  logic pipeline_valid;
  logic pipeline_ready;

  cc_stream_join #(
    .NumStreams(2)
  ) u_cc_stream_join_output (
    .i_select({metadata_connect, 1'b1}),
    .i_valid ({loop_metadata_valid, dp_command_valid}),
    .o_ready ({loop_metadata_ready, dp_command_ready}),
    .o_valid (pipeline_valid),
    .i_ready (pipeline_ready)
  );

  logic load_output;

  cc_stream_pipe_load #(
    .NumStages(1)
  ) u_cc_stream_pipe_load_output (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_valid(pipeline_valid),
    .o_ready(pipeline_ready),
    .o_load (load_output),
    .o_state(/* not used */), // ASO-UNUSED_OUTPUT : No onservability needed.
    .o_valid(o_dp_command_valid),
    .i_ready(i_dp_command_ready)
  );

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      o_dp_command_data       <= dp_command_t'(0);
      o_dp_command_metadata   <= aic_dp_cmd_gen_pkg::metadata_t'(0);
      o_dp_command_iterations <= aic_dp_cmd_gen_pkg::loop_iterations_t'(0);
      o_dp_command_last       <= 1'b0;
    end else if (load_output) begin
      o_dp_command_data       <= dp_command_data;
      o_dp_command_metadata   <= loop_metadata;
      o_dp_command_iterations <= dp_command_sideband.iterations;
      o_dp_command_last       <= dp_command_sideband.last;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON
    import axe_dv_properties_pkg::*;

    // Flush
    property p_no_flush;
      @(posedge i_clk)
      disable iff (!i_rst_n) i_flush === 1'b0;
    endproperty : p_no_flush
    check_no_flush : assume property(p_no_flush) else $error("Unexpected flush - not supported");

    // CMDB Interface
    check_cmdb_valid_ready_handshake              : assert property (p_valid_ready_handshake(i_clk,
                                                                                             i_rst_n,
                                                                                             i_cmdb_valid,
                                                                                             o_cmdb_ready));
    check_cmdb_valid_ready_deassert               : assert property (p_valid_ready_deassert(i_clk,
                                                                                            i_rst_n,
                                                                                            i_cmdb_valid,
                                                                                            o_cmdb_ready));
    check_cmdb_valid_ready_command_stable         : assert property (p_valid_ready_stable(i_clk,
                                                                                          i_rst_n,
                                                                                          i_cmdb_valid,
                                                                                          o_cmdb_ready,
                                                                                          i_cmdb_command));
    check_cmdb_valid_ready_format_stable          : assert property (p_valid_ready_stable(i_clk,
                                                                                          i_rst_n,
                                                                                          i_cmdb_valid,
                                                                                          o_cmdb_ready,
                                                                                          i_cmdb_format));

    // CMDB Interface
    check_command_valid_ready_handshake           : assert property (p_valid_ready_handshake(i_clk,
                                                                                             i_rst_n,
                                                                                             o_dp_command_valid,
                                                                                             i_dp_command_ready));
    check_command_valid_ready_deassert            : assert property (p_valid_ready_deassert(i_clk,
                                                                                            i_rst_n,
                                                                                            o_dp_command_valid,
                                                                                            i_dp_command_ready));
    check_command_valid_ready_data_stable         : assert property (p_valid_ready_stable(i_clk,
                                                                                          i_rst_n,
                                                                                          o_dp_command_valid,
                                                                                          i_dp_command_ready,
                                                                                          o_dp_command_data));
    check_command_valid_ready_metadata_stable     : assert property (p_valid_ready_stable(i_clk,
                                                                                          i_rst_n,
                                                                                          o_dp_command_valid,
                                                                                          i_dp_command_ready,
                                                                                          o_dp_command_metadata));
    check_command_valid_ready_iterations_stable   : assert property (p_valid_ready_stable(i_clk,
                                                                                          i_rst_n,
                                                                                          o_dp_command_valid,
                                                                                          i_dp_command_ready,
                                                                                          o_dp_command_iterations));
    check_command_valid_ready_last_stable         : assert property (p_valid_ready_stable(i_clk,
                                                                                          i_rst_n,
                                                                                          o_dp_command_valid,
                                                                                          i_dp_command_ready,
                                                                                          o_dp_command_last));

    // Done -> Done
    property p_command_done;
      @(posedge i_clk)
      disable iff (!i_rst_n)
      o_cmdb_done === (i_dp_done || |o_errors);
    endproperty : p_command_done
    check_p_command_done : assert property (p_command_done);

    // Bypass
    property p_bypass_always_last;
      @(posedge i_clk)
      disable iff (!i_rst_n)
      (o_dp_command_valid && (o_dp_command_metadata.format == aic_dp_cmd_gen_pkg::Bypass)) |-> o_dp_command_last;
    endproperty : p_bypass_always_last
    check_p_bypass_always_last : assert property (p_bypass_always_last);

    property p_bypass_data_is_zero;
      @(posedge i_clk)
      disable iff (!i_rst_n)
      (o_dp_command_valid && (o_dp_command_metadata.format == aic_dp_cmd_gen_pkg::Bypass)) |-> (o_dp_command_data === '0);
    endproperty : p_bypass_data_is_zero
    check_p_bypass_data_is_zero : assert property (p_bypass_data_is_zero);
  `endif
  `endif
endmodule
