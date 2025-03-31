// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// The top-level `aic_cd` glues the whole functionality together and instantiates the relevant sub-units.
///
/// ![AIC_CD: Top-Level Block-Diagram](./figures/aic_cd.drawio.svg)
///
/// !!! abstract "Design Philosophy"
///
///      Functionality is encapsulated in small units which communicate via *AXI-style* `valid / ready`
///      handshaking.  Each subunit is focused on doing one task only.  The overall functionality emmerges
///      via connecting them together.  This makes it easy to increase performance by adding buffers and
///      pipelines at strategic points in the design without woringni about internal control handshaking.
///
///
/// We reuse the common command setup found thoughout the AI-Core.  However we only use the `commandblock` as
/// the unit employs it's own synchronization scheme.
///
/// ## Description
///
/// The unit features an `AXI` subordinate and manager port.  The subordinate has two endpoints and is used
/// to configure the `aic_cd` via the [CSR registers](../build_reg/aic_cd_csr_regs.md) and the *comdblockfifo*.
/// In essence this unit consumes a command which contains information about where to find it's own instructions.
/// These are grouped as a `task_list`.  For command and instruction encodings see [here](../instructions.md).
///
/// Overall the design can be grouped into the following blocks where data flows genreally from one unit to the
/// next. For details see the respective sub-units:
///
/// 1. [CSRs](../build_reg/aic_cd_csr_regs.md) and `cmdblockfifo`: Used to configure the unit and launch *task_list* execution.
/// 2. [Instruction Fetch](instruction_fetch/index.md): Get a *task_list* from memory and perform instruction validation and error handling.
/// 3. [Execute](execute.md): Take validated instructions and distribute to sub-units.  Synchronize and wait where needed.
/// 4. [Token Unit](token_unit.md): Perform all of the token handshakes.
/// 5. [Copy Unit](copy_unit/index.md): Copy programs and commands from memory to ai-core sub-unit. Perform address patching.
///
/// There also exists some sideband signals thoughout the unit to keep track of sub-unit busy states and there like.  These are used
/// to keep ordering between different instrunction types as well and error handling.
///
/// !!! info "Parameterization"
///
///     The parameterization is kept as flexible as possbile. Hoewever due to limitation of the *CSR Reggen* some of the parameters
///     require the `aic_cd_csr.hjson` to match what the unit has been instantiated with.
///
///     !!! danger "*Fixed* Parameters requiring CSR update."
///
///         - `NumDestinations`
///         - `NumPatchModeEntries`
///         - `NumPatchTableEntries`
///
///
/// !!! tip "Parameter Validation"
///
///     Where possible and needed the `aic_cd` is dotted with *elaboration time fatals* to validate the parameterization.
///     This is to ensure the unit has been instantiated with a sane parameterization.
///
module aic_cd #(
  /// The number of destinations the unit interacts with
  parameter int unsigned NumDestinations = aic_cd_csr_reg_pkg::NUM_DESTINATIONS,
  /// The number of Patch Mode entries
  parameter int unsigned NumPatchModeEntries = aic_cd_csr_reg_pkg::NUM_PATCH_MODE_ENTRIES,
  /// The number of Patch Table entries
  parameter int unsigned NumPatchTableEntries = aic_cd_csr_reg_pkg::NUM_PATCH_TABLE_ENTRIES,
  /// The number of local tokens
  parameter int unsigned NumLocalTokens = 17,
  /// The number of global tokens
  parameter int unsigned NumGlobalTokens = 7,

  /// The depth of the Command Fifo
  parameter int unsigned CommandFifoDepth = 16,
  /// The depth of the instruction buffer.
  parameter int unsigned InstructionBufferDepth = 16,
  /// The depth of the copy buffer
  parameter int unsigned CopyBufferDepth = 32,
  /// The depth of the Fill coutner FIFOs
  parameter int unsigned FillCounterDepth = 16,

  /// Use a memory for the instruction buffer
  parameter bit InstrBufferUsesMacro = 1'b1,
  /// Memory Implementation Key for instruction fetch
  parameter InstrMemImplKey = "default",
  /// Sideband input signal type to tc_sram in the instruction fetch
  parameter type instr_ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram in the instruction fetch
  parameter type instr_ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,

  /// Use a memory for the buffer in the copy unit
  parameter bit CopyBufferUsesMacro = 1'b1,
  /// Memory Implementation Key for copy
  parameter CopyMemImplKey = "default",
  /// Sideband input signal type to tc_sram in the copy buffer
  parameter type copy_ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram in the copy buffer
  parameter type copy_ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,

  /// The ID width of the subordinate AXI port
  parameter int unsigned AxiSubIdWidth = aic_cd_defaults_pkg::AXI_S_ID_WIDTH,
  /// The Address width of the subordinate AXI port
  parameter int unsigned AxiSubAddrWidth = aic_cd_defaults_pkg::AXI_S_ADDR_WIDTH,
  /// The DATA width of the subordinate AXI port
  parameter int unsigned AxiSubDataWidth = aic_cd_defaults_pkg::AXI_S_DATA_WIDTH,

  ///Definethe part of the AXI address which should be considered for the subordinate decode
  parameter int unsigned AxiSubDecodeAddrWidth = 28,

  /// Define the axi address type for decoding
  /// Note, only use of `AxiSubDecodeAddrWidth`
  parameter type axi_decode_addr_t = logic[AxiSubDecodeAddrWidth-1:0],

  /// The start byte-axi-address of each individual endpoint
  /// Mapping:
  /// - `0: CSRs`
  /// - `1: Command FIFO`
  parameter axi_decode_addr_t AxiEndpointAddrStart[aic_cd_pkg::NUM_AXI_ENDPOINTS] = '{
      axi_decode_addr_t'('h0000),
      axi_decode_addr_t'('h1000)
  },
  /// The endpoint end address, Note the value needed here is not inclusive!
  /// I.E. If specified `'h100` the address `'0FF` will be tha last valid address.
  /// Mapping:
  /// - `0: CSRs`
  /// - `1: Command FIFO`
  parameter axi_decode_addr_t AxiEndpointAddrEnd[aic_cd_pkg::NUM_AXI_ENDPOINTS] = '{
      axi_decode_addr_t'('h1000),
      axi_decode_addr_t'('h2000)
  },

  /// AW Channel Type, subordinate port
  parameter type         axi_s_aw_t    = aic_cd_defaults_pkg::axi_s_aw_t,
  ///  W Channel Type, subordinate port
  parameter type         axi_s_w_t     = aic_cd_defaults_pkg::axi_s_w_t,
  ///  B Channel Type, subordinate port
  parameter type         axi_s_b_t     = aic_cd_defaults_pkg::axi_s_b_t,
  /// AR Channel Type, subordinate port
  parameter type         axi_s_ar_t    = aic_cd_defaults_pkg::axi_s_ar_t,
  ///  R Channel Type, subordinate port
  parameter type         axi_s_r_t     = aic_cd_defaults_pkg::axi_s_r_t,

  /// The AXI ID width of the manager AXI port
  parameter int unsigned AxiManIdWidth = aic_cd_defaults_pkg::AXI_M_ID_WIDTH,
  /// The Concrete AXI ID to use for instruction fetch AXI transactions
  parameter logic [AxiManIdWidth-1:0] AxiIdForFetch = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(0),
  /// The Concrete AXI ID to use for command and program copy AXI transactions
  parameter logic [AxiManIdWidth-1:0] AxiIdForCopy = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(1),
  /// The Address width of the manager AXI port
  parameter int unsigned AxiManAddrWidth = aic_cd_defaults_pkg::AXI_M_ADDR_WIDTH,
  /// The Data width of the manager AXI port
  parameter int unsigned AxiManDataWidth = aic_cd_defaults_pkg::AXI_M_DATA_WIDTH,

  /// Add a spill register on the manager AW port
  parameter bit CutAxiManAw = 1'b0,
  /// Add a spill register on the manager W port
  parameter bit CutAxiManW  = 1'b0,
  /// Add a spill register on the manager B port
  parameter bit CutAxiManB  = 1'b0,
  /// Add a spill register on the manager AR port
  parameter bit CutAxiManAr = 1'b0,
  /// Add a spill register on the manager R port
  parameter bit CutAxiManR  = 1'b0,

  /// AW Channel Type, manager port
  parameter type         axi_m_aw_t    = aic_cd_defaults_pkg::axi_m_aw_t,
  ///  W Channel Type, manager port
  parameter type         axi_m_w_t     = aic_cd_defaults_pkg::axi_m_w_t,
  ///  B Channel Type, manager port
  parameter type         axi_m_b_t     = aic_cd_defaults_pkg::axi_m_b_t,
  /// AR Channel Type, manager port
  parameter type         axi_m_ar_t    = aic_cd_defaults_pkg::axi_m_ar_t,
  ///  R Channel Type, manager port
  parameter type         axi_m_r_t     = aic_cd_defaults_pkg::axi_m_r_t
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_s_aw_t i_axi_s_aw,
  input  logic      i_axi_s_aw_valid,
  output logic      o_axi_s_aw_ready,
  input  axi_s_w_t  i_axi_s_w,
  input  logic      i_axi_s_w_valid,
  output logic      o_axi_s_w_ready,
  output axi_s_b_t  o_axi_s_b,
  output logic      o_axi_s_b_valid,
  input  logic      i_axi_s_b_ready,
  input  axi_s_ar_t i_axi_s_ar,
  input  logic      i_axi_s_ar_valid,
  output logic      o_axi_s_ar_ready,
  output axi_s_r_t  o_axi_s_r,
  output logic      o_axi_s_r_valid,
  input  logic      i_axi_s_r_ready,

  //////////////////
  // Manager port //
  //////////////////
  output axi_m_aw_t o_axi_m_aw,
  output logic      o_axi_m_aw_valid,
  input  logic      i_axi_m_aw_ready,
  output axi_m_w_t  o_axi_m_w,
  output logic      o_axi_m_w_valid,
  input  logic      i_axi_m_w_ready,
  input  axi_m_b_t  i_axi_m_b,
  input  logic      i_axi_m_b_valid,
  output logic      o_axi_m_b_ready,
  output axi_m_ar_t o_axi_m_ar,
  output logic      o_axi_m_ar_valid,
  input  logic      i_axi_m_ar_ready,
  input  axi_m_r_t  i_axi_m_r,
  input  logic      i_axi_m_r_valid,
  output logic      o_axi_m_r_ready,

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
  output logic [NumGlobalTokens-1:0] o_token_global_cons_ready,

  ///////////////
  // Timestamp //
  ///////////////
  /// The id of the timestamp
  output aic_cd_pkg::timestamp_trigger_id_t o_timestamp_id,
  /// The pulse that the timestamp is active
  output logic                              o_timestamp_active_pulse,

  ////////////////////////////////////////////////
  // Syncronization lines from the destinations //
  ////////////////////////////////////////////////
  /// A destination as completed a command, these cause the fill counters to decrement
  input  logic [NumDestinations-1:0] i_destination_cmd_done,

  ///////////////////
  // Configuration //
  ///////////////////
  /// Global base address added to any transaction generated by the manager port
  ///
  /// This should match the base address of the respective AI core
  input  logic [AxiManAddrWidth-1:0] i_aic_base_addr,

  ///////////////
  // Interrupt //
  ///////////////
  /// An interrupt is raised
  output logic o_irq,

  /////////////////////////////
  // Memory Sideband Signals //
  /////////////////////////////
  /// Memory sideband input signals (tie to `'0` if `BufferUsesMacro == 1'b0`)
  input  instr_ram_impl_inp_t i_instr_ram_impl,
  /// Memory sideband output signals
  output instr_ram_impl_oup_t o_instr_ram_impl,
  /// Memory sideband input signals (tie to `'0` if `BufferUsesMacro == 1'b0`)
  input  copy_ram_impl_inp_t  i_copy_ram_impl,
  /// Memory sideband output signals
  output copy_ram_impl_oup_t  o_copy_ram_impl

);

  ///////////////////////////////
  // AXI Subordinate and Demux //
  ///////////////////////////////
  localparam int unsigned AxiSubStrbWidth = AxiSubDataWidth / 8;
  typedef logic [AxiSubIdWidth  -1:0] axi_s_id_t;
  typedef logic [AxiSubAddrWidth-1:0] axi_s_addr_t;
  typedef logic [AxiSubDataWidth-1:0] axi_s_data_t;
  typedef logic [AxiSubStrbWidth-1:0] axi_s_strb_t;

  // The extra endpoint is needed to propagatedecode errors
  localparam int unsigned EndpointIndexWidth = cc_math_pkg::index_width(aic_cd_pkg::NUM_AXI_ENDPOINTS + 1);
  typedef logic [EndpointIndexWidth-1:0] endpoint_index_t;

  // The index for a decode error is all 1
  localparam endpoint_index_t DecodeErrorIndex = {EndpointIndexWidth{1'b1}};

  // Address map entry definition
  typedef struct packed {
    endpoint_index_t  index;
    axi_decode_addr_t addr_start;
    axi_decode_addr_t addr_end;
  } address_rule_t;

  address_rule_t address_map[aic_cd_pkg::NUM_AXI_ENDPOINTS];
  always_comb begin
    address_map[aic_cd_pkg::ENDPOINT_CSR] = '{
      index:      endpoint_index_t'(aic_cd_pkg::ENDPOINT_CSR),
      addr_start: axi_decode_addr_t'(AxiEndpointAddrStart[aic_cd_pkg::ENDPOINT_CSR]),
      addr_end:   axi_decode_addr_t'(AxiEndpointAddrEnd[aic_cd_pkg::ENDPOINT_CSR])
    };
    address_map[aic_cd_pkg::ENDPOINT_CMD] = '{
      index:      endpoint_index_t'(aic_cd_pkg::ENDPOINT_CMD),
      addr_start: axi_decode_addr_t'(AxiEndpointAddrStart[aic_cd_pkg::ENDPOINT_CMD]),
      addr_end:   axi_decode_addr_t'(AxiEndpointAddrEnd[aic_cd_pkg::ENDPOINT_CMD])
    };
  end

  endpoint_index_t ext_mt_sel_rd, ext_mt_sel_wr;

  cc_decode_addr #(
    .NumRules(aic_cd_pkg::NUM_AXI_ENDPOINTS),
    .index_t (endpoint_index_t),
    .addr_t  (axi_decode_addr_t),
    .rule_t  (address_rule_t)
  ) u_cc_decode_addr_aw (
    .i_address         (axi_decode_addr_t'(i_axi_s_aw.addr)),
    .i_address_map     (address_map),
    .o_index           (ext_mt_sel_wr),
    .o_decode_valid    (/* not used */),
    .o_decode_error    (/* not used */),
    .i_default_index_en(1'b1),
    .i_default_index   (DecodeErrorIndex),
    .i_config_ongoing  (1'b0)
  );

  cc_decode_addr #(
    .NumRules(aic_cd_pkg::NUM_AXI_ENDPOINTS),
    .index_t (endpoint_index_t),
    .addr_t  (axi_decode_addr_t),
    .rule_t  (address_rule_t)
  ) u_cc_decode_addr_ar (
    .i_address         (axi_decode_addr_t'(i_axi_s_ar.addr)),
    .i_address_map     (address_map),
    .o_index           (ext_mt_sel_rd),
    .o_decode_valid    (/* not used */),
    .o_decode_error    (/* not used */),
    .i_default_index_en(1'b1),
    .i_default_index   (DecodeErrorIndex),
    .i_config_ongoing  (1'b0)
  );

  axi_s_id_t           [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_id;
  axi_pkg::axi_len_t   [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_len;
  axi_s_addr_t         [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_addr;
  axi_pkg::axi_size_t  [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_size;
  axi_pkg::axi_burst_t [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_burst;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_valid;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_aw_ready;

  axi_s_data_t         [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_w_data;
  axi_s_strb_t         [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_w_strb;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_w_last;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_w_valid;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_w_ready;

  axi_s_id_t           [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_b_id;
  axi_pkg::axi_resp_t  [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_b_resp;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_b_valid;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_b_ready;

  axi_s_id_t           [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_id;
  axi_pkg::axi_len_t   [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_len;
  axi_s_addr_t         [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_addr;
  axi_pkg::axi_size_t  [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_size;
  axi_pkg::axi_burst_t [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_burst;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_valid;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_ar_ready;

  axi_s_id_t           [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_r_id;
  axi_s_data_t         [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_r_data;
  axi_pkg::axi_resp_t  [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_r_resp;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_r_last;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_r_valid;
  logic                [aic_cd_pkg::NUM_AXI_ENDPOINTS-1:0] axi_s_r_ready;

  simple_axi_demux #(
    .NR_MASTERS     (aic_cd_pkg::NUM_AXI_ENDPOINTS),
    .IDW            (AxiSubIdWidth),
    .AW             (AxiSubAddrWidth),
    .DW             (AxiSubDataWidth),
    .BW             (axi_pkg::AXI_LEN_WIDTH),
    .SL_WREQ_SHIELD (2),
    .SL_RREQ_SHIELD (2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR            (4),
    .EXT_SEL        (1'b1)
  ) u_simple_axi_demux (
    .i_clk,
    .i_rst_n,
    .i_ext_mt_sel_rd(ext_mt_sel_rd),
    .i_ext_mt_sel_wr(ext_mt_sel_wr),
    .s_awid         (i_axi_s_aw.id),
    .s_awaddr       (i_axi_s_aw.addr),
    .s_awlen        (i_axi_s_aw.len),
    .s_awsize       (i_axi_s_aw.size),
    .s_awburst      (i_axi_s_aw.burst),
    .s_awlock       ('0), // Not propagated downstream
    .s_awprot       ('0), // Not propagated downstream
    .s_awcache      ('0), // Not propagated downstream
    .s_awvalid      (i_axi_s_aw_valid),
    .s_awready      (o_axi_s_aw_ready),
    .s_wdata        (i_axi_s_w.data),
    .s_wstrb        (i_axi_s_w.strb),
    .s_wlast        (i_axi_s_w.last),
    .s_wvalid       (i_axi_s_w_valid),
    .s_wready       (o_axi_s_w_ready),
    .s_bid          (o_axi_s_b.id),
    .s_bresp        (o_axi_s_b.resp),
    .s_bvalid       (o_axi_s_b_valid),
    .s_bready       (i_axi_s_b_ready),
    .s_arid         (i_axi_s_ar.id),
    .s_araddr       (i_axi_s_ar.addr),
    .s_arlen        (i_axi_s_ar.len),
    .s_arsize       (i_axi_s_ar.size),
    .s_arburst      (i_axi_s_ar.burst),
    .s_arlock       ('0), // Not propagated downstream
    .s_arprot       ('0), // Not propagated downstream
    .s_arcache      ('0), // Not propagated downstream
    .s_arvalid      (i_axi_s_ar_valid),
    .s_arready      (o_axi_s_ar_ready),
    .s_rid          (o_axi_s_r.id),
    .s_rdata        (o_axi_s_r.data),
    .s_rresp        (o_axi_s_r.resp),
    .s_rlast        (o_axi_s_r.last),
    .s_rvalid       (o_axi_s_r_valid),
    .s_rready       (i_axi_s_r_ready),
    .m_awid         (axi_s_aw_id),
    .m_awlen        (axi_s_aw_len),
    .m_awaddr       (axi_s_aw_addr),
    .m_awsize       (axi_s_aw_size),
    .m_awburst      (axi_s_aw_burst),
    .m_awlock       (/* not used */),
    .m_awprot       (/* not used */),
    .m_awcache      (/* not used */),
    .m_awvalid      (axi_s_aw_valid),
    .m_awready      (axi_s_aw_ready),
    .m_wdata        (axi_s_w_data),
    .m_wstrb        (axi_s_w_strb),
    .m_wlast        (axi_s_w_last),
    .m_wvalid       (axi_s_w_valid),
    .m_wready       (axi_s_w_ready),
    .m_bid          (axi_s_b_id),
    .m_bresp        (axi_s_b_resp),
    .m_bvalid       (axi_s_b_valid),
    .m_bready       (axi_s_b_ready),
    .m_arid         (axi_s_ar_id),
    .m_arlen        (axi_s_ar_len),
    .m_araddr       (axi_s_ar_addr),
    .m_arsize       (axi_s_ar_size),
    .m_arburst      (axi_s_ar_burst),
    .m_arlock       (/* not used */),
    .m_arprot       (/* not used */),
    .m_arcache      (/* not used */),
    .m_arvalid      (axi_s_ar_valid),
    .m_arready      (axi_s_ar_ready),
    .m_rid          (axi_s_r_id),
    .m_rdata        (axi_s_r_data),
    .m_rresp        (axi_s_r_resp),
    .m_rlast        (axi_s_r_last),
    .m_rvalid       (axi_s_r_valid),
    .m_rready       (axi_s_r_ready)
  );

  //////////////////////////////////
  // Control and Status Registers //
  //////////////////////////////////
  if (NumDestinations      != aic_cd_csr_reg_pkg::NUM_DESTINATIONS)
    $fatal(1, "Parameter: 'NumDestinations' not matching aic_cd_csr_reg_pkg::NUM_DESTINATIONS;");
  if (NumPatchModeEntries  != aic_cd_csr_reg_pkg::NUM_PATCH_MODE_ENTRIES)
    $fatal(1, "Parameter: 'NumPatchModeEntries' not matching aic_cd_csr_reg_pkg::NUM_PATCH_MODE_ENTRIES;");
  if (NumPatchTableEntries != aic_cd_csr_reg_pkg::NUM_PATCH_TABLE_ENTRIES)
    $fatal(1, "Parameter: 'NumPatchTableEntries' not matching aic_cd_csr_reg_pkg::NUM_PATCH_TABLE_ENTRIES;");

  aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_t csr_reg2hw;  // reading
  aic_cd_csr_reg_pkg::aic_cd_csr_hw2reg_t csr_hw2reg;  // writing

  aic_cd_csr_reg_pkg::axi_a_ch_h2d_t axi_csr_aw;
  aic_cd_csr_reg_pkg::axi_a_ch_h2d_t axi_csr_ar;
  aic_cd_csr_reg_pkg::axi_w_ch_h2d_t axi_csr_w;
  aic_cd_csr_reg_pkg::axi_r_ch_d2h_t axi_csr_r;
  aic_cd_csr_reg_pkg::axi_b_ch_d2h_t axi_csr_b;

  if ($bits(i_axi_s_aw.id) != $bits(axi_csr_aw.id))
      $fatal(1, "Width of i_axi_s_aw.id (%d) not matching  axi_csr_aw.id(%d)", $bits(i_axi_s_aw.id), $bits(axi_csr_aw.id));
  if ($bits(i_axi_s_aw.addr) != $bits(axi_csr_aw.addr))
      $fatal(1, "Width of i_axi_s_aw.addr (%d) not matching  axi_csr_aw.addr(%d)", $bits(i_axi_s_aw.addr), $bits(axi_csr_aw.addr));
  if ($bits(i_axi_s_aw.len) != $bits(axi_csr_aw.len))
      $fatal(1, "Width of i_axi_s_aw.len (%d) not matching  axi_csr_aw.len(%d)", $bits(i_axi_s_aw.len), $bits(axi_csr_aw.len));
  if ($bits(i_axi_s_w.data) != $bits(axi_csr_w.data))
      $fatal(1, "Width of i_axi_s_w.data (%d) not matching  axi_csr_w.data(%d)", $bits(i_axi_s_w.data), $bits(axi_csr_w.data));
  if ($bits(o_axi_s_b.id) != $bits(axi_csr_b.id))
      $fatal(1, "Width of o_axi_s_b.id (%d) not matching  axi_csr_b.id(%d)", $bits(o_axi_s_b.id), $bits(axi_csr_b.id));

  if ($bits(i_axi_s_ar.id) != $bits(axi_csr_ar.id))
      $fatal(1, "Width of i_axi_s_ar.id (%d) not matching  axi_csr_ar.id(%d)", $bits(i_axi_s_ar.id), $bits(axi_csr_ar.id));
  if ($bits(i_axi_s_ar.addr) != $bits(axi_csr_ar.addr))
      $fatal(1, "Width of i_axi_s_ar.addr (%d) not matching  axi_csr_ar.addr(%d)", $bits(i_axi_s_ar.addr), $bits(axi_csr_ar.addr));
  if ($bits(i_axi_s_ar.len) != $bits(axi_csr_ar.len))
      $fatal(1, "Width of i_axi_s_ar.len (%d) not matching  axi_csr_ar.len(%d)", $bits(i_axi_s_ar.len), $bits(axi_csr_ar.len));
  if ($bits(o_axi_s_r.id) != $bits(axi_csr_r.id))
      $fatal(1, "Width of o_axi_s_r.id (%d) not matching  axi_csr_r.id(%d)", $bits(o_axi_s_r.id), $bits(axi_csr_r.id));
  if ($bits(o_axi_s_r.data) != $bits(axi_csr_r.data))
      $fatal(1, "Width of o_axi_s_r.data (%d) not matching  axi_csr_r.data(%d)", $bits(o_axi_s_r.data), $bits(axi_csr_r.data));

  always_comb axi_csr_aw = '{
    id:    axi_s_aw_id[aic_cd_pkg::ENDPOINT_CSR],
    addr:  axi_s_aw_addr[aic_cd_pkg::ENDPOINT_CSR],
    len:   axi_s_aw_len[aic_cd_pkg::ENDPOINT_CSR],
    size:  axi_s_aw_size[aic_cd_pkg::ENDPOINT_CSR],
    burst: axi_s_aw_burst[aic_cd_pkg::ENDPOINT_CSR],
    valid: axi_s_aw_valid[aic_cd_pkg::ENDPOINT_CSR]
  };

  always_comb axi_csr_w = '{
    data:  axi_s_w_data[aic_cd_pkg::ENDPOINT_CSR],
    strb:  axi_s_w_strb[aic_cd_pkg::ENDPOINT_CSR],
    last:  axi_s_w_last[aic_cd_pkg::ENDPOINT_CSR],
    valid: axi_s_w_valid[aic_cd_pkg::ENDPOINT_CSR]
  };

  always_comb axi_s_b_id[aic_cd_pkg::ENDPOINT_CSR]   = axi_csr_b.id;
  always_comb axi_s_b_resp[aic_cd_pkg::ENDPOINT_CSR] = axi_csr_b.resp;
  always_comb axi_s_b_valid[aic_cd_pkg::ENDPOINT_CSR] = axi_csr_b.valid;

  always_comb axi_csr_ar = '{
    id:    axi_s_ar_id[aic_cd_pkg::ENDPOINT_CSR],
    addr:  axi_s_ar_addr[aic_cd_pkg::ENDPOINT_CSR],
    len:   axi_s_ar_len[aic_cd_pkg::ENDPOINT_CSR],
    size:  axi_s_ar_size[aic_cd_pkg::ENDPOINT_CSR],
    burst: axi_s_ar_burst[aic_cd_pkg::ENDPOINT_CSR],
    valid: axi_s_ar_valid[aic_cd_pkg::ENDPOINT_CSR]
  };

  always_comb axi_s_r_id[aic_cd_pkg::ENDPOINT_CSR]    = axi_csr_r.id;
  always_comb axi_s_r_data[aic_cd_pkg::ENDPOINT_CSR]  = axi_csr_r.data;
  always_comb axi_s_r_resp[aic_cd_pkg::ENDPOINT_CSR]  = axi_csr_r.resp;
  always_comb axi_s_r_last[aic_cd_pkg::ENDPOINT_CSR]  = axi_csr_r.last;
  always_comb axi_s_r_valid[aic_cd_pkg::ENDPOINT_CSR] = axi_csr_r.valid;

  aic_cd_csr_reg_top u_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    .axi_aw_i   (axi_csr_aw),
    .axi_awready(axi_s_aw_ready[aic_cd_pkg::ENDPOINT_CSR]),
    .axi_w_i    (axi_csr_w),
    .axi_wready (axi_s_w_ready[aic_cd_pkg::ENDPOINT_CSR]),
    .axi_b_o    (axi_csr_b),
    .axi_bready (axi_s_b_ready[aic_cd_pkg::ENDPOINT_CSR]),
    .axi_ar_i   (axi_csr_ar),
    .axi_arready(axi_s_ar_ready[aic_cd_pkg::ENDPOINT_CSR]),
    .axi_r_o    (axi_csr_r),
    .axi_rready (axi_s_r_ready[aic_cd_pkg::ENDPOINT_CSR]),
    .reg2hw     (csr_reg2hw),
    .hw2reg     (csr_hw2reg),
    .devmode_i  (1'b1)
  );

  // Connect hardware capability constants
  assign csr_hw2reg.hw_capability_params.num_destinations.d        = 8'(NumDestinations);
  assign csr_hw2reg.hw_capability_params.num_patch_mode_entries.d  = 8'(NumPatchModeEntries);
  assign csr_hw2reg.hw_capability_params.num_patch_table_entries.d = 8'(NumPatchTableEntries);
  assign csr_hw2reg.hw_capability_params.num_local_tokens.d        = 8'(NumLocalTokens);
  assign csr_hw2reg.hw_capability_params.num_global_tokens.d       = 8'(NumGlobalTokens);

  assign csr_hw2reg.hw_capability_fifos.command_fifo_depth.d       = 8'(CommandFifoDepth);
  assign csr_hw2reg.hw_capability_fifos.instruction_buffer_depth.d = 8'(InstructionBufferDepth);
  assign csr_hw2reg.hw_capability_fifos.copy_buffer_depth.d        = 8'(CopyBufferDepth);
  assign csr_hw2reg.hw_capability_fifos.fill_coutner_depth.d       = 8'(FillCounterDepth);

  //////////////////
  // Command FIFO //
  //////////////////
  aic_cd_pkg::aic_cd_command_t command;
  logic                        command_valid;
  logic                        command_ready;

  localparam int unsigned COMMAND_NUM_FIELDS = 3;
  localparam int unsigned CommandFieldLsbIdx[COMMAND_NUM_FIELDS] = {
    32'd0,
    aic_cd_pkg::TASK_LIST_POINTER_WIDTH,
    aic_cd_pkg::TASK_LIST_POINTER_WIDTH + aic_cd_pkg::TASK_LIST_LENGTH_WIDTH
  };
  localparam int unsigned CommandFieldSize[COMMAND_NUM_FIELDS] = {
    aic_cd_pkg::TASK_LIST_POINTER_WIDTH,
    aic_cd_pkg::TASK_LIST_LENGTH_WIDTH,
    aic_cd_pkg::CONTROL_OFFSET_WIDTH
  };

  cmdblock_cmd_fifo #(
    .IDW           (AxiSubIdWidth),
    .AW            (AxiSubAddrWidth),
    .DW            (AxiSubDataWidth),
    .OUT_DW        (aic_cd_pkg::AicCdCommandWidth),
    .BW            (axi_pkg::AXI_LEN_WIDTH),
    .NR_FORMATS    (1),
    .NR_FIELDS     (COMMAND_NUM_FIELDS),
    .FIELD_LSB_IDX (CommandFieldLsbIdx),
    .FIELD_SIZE    (CommandFieldSize),
    .CMD_FIFO_DEPTH(CommandFifoDepth),
    .CMD_FIFO_WIDTH(aic_cd_pkg::AicCdCommandWidth),
    .USE_MACRO     (0)
  ) u_cmdblock_cmd_fifo (
    .i_clk,
    .i_rst_n,
    .exec          (csr_reg2hw.command_control.exec_en.q),
    .pointer_rst   (csr_reg2hw.command_control.ptr_rst.q),
    .cur_pointer   (csr_hw2reg.command_status.in_word_ptr.d),
    .cur_fifo_count(csr_hw2reg.command_status.fifo_cnt.d),
    .cmd_dropped   (csr_hw2reg.irq_status.command_dropped.de),
    .awid          (axi_s_aw_id[aic_cd_pkg::ENDPOINT_CMD]),
    .awaddr        (axi_s_aw_addr[aic_cd_pkg::ENDPOINT_CMD]),
    .awlen         (axi_s_aw_len[aic_cd_pkg::ENDPOINT_CMD]),
    .awsize        (axi_s_aw_size[aic_cd_pkg::ENDPOINT_CMD]),
    .awburst       (axi_s_aw_burst[aic_cd_pkg::ENDPOINT_CMD]),
    .awvalid       (axi_s_aw_valid[aic_cd_pkg::ENDPOINT_CMD]),
    .awready       (axi_s_aw_ready[aic_cd_pkg::ENDPOINT_CMD]),
    .wdata         (axi_s_w_data[aic_cd_pkg::ENDPOINT_CMD]),
    .wstrb         (axi_s_w_strb[aic_cd_pkg::ENDPOINT_CMD]),
    .wlast         (axi_s_w_last[aic_cd_pkg::ENDPOINT_CMD]),
    .wvalid        (axi_s_w_valid[aic_cd_pkg::ENDPOINT_CMD]),
    .wready        (axi_s_w_ready[aic_cd_pkg::ENDPOINT_CMD]),
    .bid           (axi_s_b_id[aic_cd_pkg::ENDPOINT_CMD]),
    .bresp         (axi_s_b_resp[aic_cd_pkg::ENDPOINT_CMD]),
    .bvalid        (axi_s_b_valid[aic_cd_pkg::ENDPOINT_CMD]),
    .bready        (axi_s_b_ready[aic_cd_pkg::ENDPOINT_CMD]),
    .arid          (axi_s_ar_id[aic_cd_pkg::ENDPOINT_CMD]),
    .araddr        (axi_s_ar_addr[aic_cd_pkg::ENDPOINT_CMD]),
    .arlen         (axi_s_ar_len[aic_cd_pkg::ENDPOINT_CMD]),
    .arsize        (axi_s_ar_size[aic_cd_pkg::ENDPOINT_CMD]),
    .arburst       (axi_s_ar_burst[aic_cd_pkg::ENDPOINT_CMD]),
    .arvalid       (axi_s_ar_valid[aic_cd_pkg::ENDPOINT_CMD]),
    .arready       (axi_s_ar_ready[aic_cd_pkg::ENDPOINT_CMD]),
    .rid           (axi_s_r_id[aic_cd_pkg::ENDPOINT_CMD]),
    .rdata         (axi_s_r_data[aic_cd_pkg::ENDPOINT_CMD]),
    .rresp         (axi_s_r_resp[aic_cd_pkg::ENDPOINT_CMD]),
    .rlast         (axi_s_r_last[aic_cd_pkg::ENDPOINT_CMD]),
    .rvalid        (axi_s_r_valid[aic_cd_pkg::ENDPOINT_CMD]),
    .rready        (axi_s_r_ready[aic_cd_pkg::ENDPOINT_CMD]),
    .cmd_data      (command),
    .cmd_format    (/* not used */),
    .cmd_vld       (command_valid),
    .cmd_rdy       (command_ready)
  );

  //////////////////////////////////////
  // Instruction Fetch and Validation //
  //////////////////////////////////////
  logic                                       drop_instructions;
  aic_cd_pkg::instruction_validation_errors_t error_instruction_validation;

  axi_m_ar_t axi_instruction_ar;
  logic      axi_instruction_ar_valid;
  logic      axi_instruction_ar_ready;
  axi_m_r_t  axi_instruction_r;
  logic      axi_instruction_r_valid;
  logic      axi_instruction_r_ready;

  aic_cd_pkg::instruction_t           instruction;
  aic_cd_pkg::control_offset_t        instruction_control_offset;
  aic_cd_pkg::task_list_word_length_t instruction_index;
  logic                               instruction_last;
  logic                               instruction_valid;
  logic                               instruction_ready;

  aic_cd_instruction_fetch #(
    .NumDestinations       (NumDestinations),
    .NumPatchModeEntries   (NumPatchModeEntries),
    .NumPatchTableEntries  (NumPatchTableEntries),
    .NumLocalTokens        (NumLocalTokens),
    .NumGlobalTokens       (NumGlobalTokens),
    .AxiIdWidth            (AxiManIdWidth),
    .AxiIdForFetch         (AxiIdForFetch),
    .AxiAddrWidth          (AxiManAddrWidth),
    .InstructionBufferDepth(InstructionBufferDepth),
    .axi_ar_t              (axi_m_ar_t),
    .axi_r_t               (axi_m_r_t),
    .BufferUsesMacro       (InstrBufferUsesMacro),
    .MemImplKey            (InstrMemImplKey),
    .ram_impl_inp_t        (instr_ram_impl_inp_t),
    .ram_impl_oup_t        (instr_ram_impl_oup_t)
  ) u_aic_cd_instruction_fetch (
    .i_clk,
    .i_rst_n,
    .i_aic_base_addr               (axi_pkg::axi_largest_addr_t'(i_aic_base_addr)),
    .i_ctrl_data_base_addr         (axi_pkg::axi_largest_addr_t'(csr_reg2hw.ctrl_data_base_addr.q)),
    .i_command                     (command),
    .i_command_valid               (command_valid),
    .o_command_ready               (command_ready),
    .o_axi_m_ar                    (axi_instruction_ar),
    .o_axi_m_ar_valid              (axi_instruction_ar_valid),
    .i_axi_m_ar_ready              (axi_instruction_ar_ready),
    .i_axi_m_r                     (axi_instruction_r),
    .i_axi_m_r_valid               (axi_instruction_r_valid),
    .o_axi_m_r_ready               (axi_instruction_r_ready),
    .o_instruction                 (instruction),
    .o_instruction_control_offset  (instruction_control_offset),
    .o_instruction_index           (instruction_index),
    .o_instruction_last            (instruction_last),
    .o_instruction_valid           (instruction_valid),
    .i_instruction_ready           (instruction_ready),
    .i_drop_instructions           (drop_instructions),
    .o_request_busy                (csr_hw2reg.status_busy.instr_request.d),
    .o_axi_read_busy               (csr_hw2reg.status_busy.instr_axi_read.d),
    .o_validation_busy             (csr_hw2reg.status_busy.instr_validate.d),
    .o_error_empty_task_list       (csr_hw2reg.irq_status.command_empty_task_list.de),
    .o_error_instruction_validation(error_instruction_validation),
    .i_ram_impl                    (i_instr_ram_impl),
    .o_ram_impl                    (o_instr_ram_impl)
  );

  assign csr_hw2reg.irq_status.instr_axi_resp_slverr.de        = error_instruction_validation.axi_response_slverr;
  assign csr_hw2reg.irq_status.instr_axi_resp_decerr.de        = error_instruction_validation.axi_response_decerr;
  assign csr_hw2reg.irq_status.instr_dst_id_mapping.de         = error_instruction_validation.destination_id_mapping;
  assign csr_hw2reg.irq_status.instr_patch_mode_mapping.de     = error_instruction_validation.patch_mode_mapping;
  assign csr_hw2reg.irq_status.instr_patch_id_0_mapping.de     = error_instruction_validation.patch_id_0_mapping;
  assign csr_hw2reg.irq_status.instr_patch_id_1_mapping.de     = error_instruction_validation.patch_id_1_mapping;
  assign csr_hw2reg.irq_status.instr_token_illegal_opcode.de   = error_instruction_validation.token_illegal_opcode;
  assign csr_hw2reg.irq_status.instr_token_local_map_empty.de  = error_instruction_validation.token_local_map_empty;
  assign csr_hw2reg.irq_status.instr_token_global_map_empty.de = error_instruction_validation.token_global_map_empty;
  assign csr_hw2reg.irq_status.instr_token_local_mapping.de    = error_instruction_validation.token_local_mapping;
  assign csr_hw2reg.irq_status.instr_token_global_mapping.de   = error_instruction_validation.token_global_mapping;


  /////////////
  // Execute //
  /////////////
  axi_pkg::axi_largest_addr_t destination_addr_command[NumDestinations];
  axi_pkg::axi_largest_addr_t destination_addr_program[NumDestinations];

  always_comb foreach (destination_addr_command[destination]) begin
    destination_addr_command[destination] = axi_pkg::axi_largest_addr_t'(csr_reg2hw.dst_addr_command[destination].q);
  end
  always_comb foreach (destination_addr_program[destination]) begin
    destination_addr_program[destination] = axi_pkg::axi_largest_addr_t'(csr_reg2hw.dst_addr_program[destination].q);
  end

  aic_cd_pkg::copy_command_t copy_command;
  logic                      copy_command_valid;
  logic                      copy_command_ready;

  aic_cd_pkg::token_opcode_e token_opcode;
  aic_cd_pkg::token_mask_t   token_mask;
  logic                      token_valid;
  logic                      token_ready;

  logic copy_unit_busy;
  always_comb copy_unit_busy =
      csr_hw2reg.status_busy.copy_read_request.d
    | csr_hw2reg.status_busy.copy_axi_read.d
    | csr_hw2reg.status_busy.copy_address_patching.d
    | csr_hw2reg.status_busy.copy_fill_counters.d
    | csr_hw2reg.status_busy.copy_axi_write_request.d;

  aic_cd_execute #(
    .NumDestinations(NumDestinations)
  ) u_aic_cd_execute (
    .i_clk,
    .i_rst_n,
    .o_busy                      (csr_hw2reg.status_busy.execute.d),
    .i_token_unit_busy           (csr_hw2reg.status_busy.token.d),
    .i_copy_unit_busy            (copy_unit_busy),
    .o_task_list_done            (csr_hw2reg.irq_status.task_list_done.de),
    .i_instruction               (instruction),
    .i_instruction_control_offset(instruction_control_offset),
    .i_instruction_index         (instruction_index),
    .i_instruction_last          (instruction_last),
    .i_instruction_valid         (instruction_valid),
    .o_instruction_ready         (instruction_ready),
    .o_copy_command              (copy_command),
    .o_copy_command_valid        (copy_command_valid),
    .i_copy_command_ready        (copy_command_ready),
    .o_token_opcode              (token_opcode),
    .o_token_mask                (token_mask),
    .o_token_valid               (token_valid),
    .i_token_ready               (token_ready),
    .o_timestamp_id,
    .o_timestamp_active_pulse,
    .i_aic_base_addr             (axi_pkg::axi_largest_addr_t'(i_aic_base_addr)),
    .i_ctrl_data_base_addr       (axi_pkg::axi_largest_addr_t'(csr_reg2hw.ctrl_data_base_addr.q)),
    .i_destination_addr_command  (destination_addr_command),
    .i_destination_addr_program  (destination_addr_program)
  );

  always_comb csr_hw2reg.status_busy.timestamp.d = o_timestamp_active_pulse;

  ////////////////
  // Token Unit //
  ////////////////
  aic_cd_token_unit #(
    .NumLocalTokens (NumLocalTokens),
    .NumGlobalTokens(NumGlobalTokens)
  ) u_aic_cd_token_unit (
    .i_clk,
    .i_rst_n,
    .o_busy                   (csr_hw2reg.status_busy.token.d),
    .i_token_opcode           (token_opcode),
    .i_token_mask             (token_mask),
    .i_token_valid            (token_valid),
    .o_token_ready            (token_ready),
    .o_token_local_prod_valid,
    .i_token_local_prod_ready,
    .i_token_local_cons_valid,
    .o_token_local_cons_ready,
    .o_token_global_prod_valid,
    .i_token_global_prod_ready,
    .i_token_global_cons_valid,
    .o_token_global_cons_ready
  );


  ///////////////
  // Copy Unit //
  ///////////////

  axi_m_aw_t axi_copy_aw;
  logic      axi_copy_aw_valid;
  logic      axi_copy_aw_ready;
  axi_m_w_t  axi_copy_w;
  logic      axi_copy_w_valid;
  logic      axi_copy_w_ready;
  axi_m_b_t  axi_copy_b;
  logic      axi_copy_b_valid;
  logic      axi_copy_b_ready;
  axi_m_ar_t axi_copy_ar;
  logic      axi_copy_ar_valid;
  logic      axi_copy_ar_ready;
  axi_m_r_t  axi_copy_r;
  logic      axi_copy_r_valid;
  logic      axi_copy_r_ready;

  logic [NumDestinations-1:0] destination_cmd_done_q;
  logic                       destination_cmd_done_load;

  always_comb destination_cmd_done_load = (destination_cmd_done_q != i_destination_cmd_done);

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                       destination_cmd_done_q <= '0;
    else if (destination_cmd_done_load) destination_cmd_done_q <= i_destination_cmd_done;
  end

  logic                               command_stalled;
  logic                               must_be_stalled[NumDestinations];
  aic_cd_pkg::command_byte_length_t   fill_count[NumDestinations];

  aic_cd_pkg::copy_errors_t           copy_errors;
  aic_cd_pkg::task_list_word_length_t copy_instruction_index;

  aic_cd_copy_unit #(
    .NumDestinations      (NumDestinations),
    .NumPatchModeEntries  (NumPatchModeEntries),
    .NumPatchTableEntries (NumPatchTableEntries),
    .AxiIdWidth           (AxiManIdWidth),
    .AxiIdForCopy         (AxiIdForCopy),
    .AxiAddrWidth         (AxiManAddrWidth),
    .AxiDataWidth         (AxiManDataWidth),
    .CopyBufferDepth      (CopyBufferDepth),
    .FillCounterDepth     (FillCounterDepth),
    .dst_cmdblock_params_t(aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_dst_cmdblock_params_mreg_t),
    .patch_mode_entry_t   (aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_patch_mode_mreg_t),
    .patch_table_entry_t  (aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_patch_table_mreg_t),
    .axi_aw_t             (axi_m_aw_t),
    .axi_w_t              (axi_m_w_t),
    .axi_b_t              (axi_m_b_t),
    .axi_ar_t             (axi_m_ar_t),
    .axi_r_t              (axi_m_r_t),
    .BufferUsesMacro      (CopyBufferUsesMacro),
    .MemImplKey           (CopyMemImplKey),
    .ram_impl_inp_t       (copy_ram_impl_inp_t),
    .ram_impl_oup_t       (copy_ram_impl_oup_t)
  ) u_aic_cd_copy_unit (
    .i_clk,
    .i_rst_n,
    .i_copy_command               (copy_command),
    .i_copy_command_valid         (copy_command_valid),
    .o_copy_command_ready         (copy_command_ready),
    .o_axi_m_aw                   (axi_copy_aw),
    .o_axi_m_aw_valid             (axi_copy_aw_valid),
    .i_axi_m_aw_ready             (axi_copy_aw_ready),
    .o_axi_m_w                    (axi_copy_w),
    .o_axi_m_w_valid              (axi_copy_w_valid),
    .i_axi_m_w_ready              (axi_copy_w_ready),
    .i_axi_m_b                    (axi_copy_b),
    .i_axi_m_b_valid              (axi_copy_b_valid),
    .o_axi_m_b_ready              (axi_copy_b_ready),
    .o_axi_m_ar                   (axi_copy_ar),
    .o_axi_m_ar_valid             (axi_copy_ar_valid),
    .i_axi_m_ar_ready             (axi_copy_ar_ready),
    .i_axi_m_r                    (axi_copy_r),
    .i_axi_m_r_valid              (axi_copy_r_valid),
    .o_axi_m_r_ready              (axi_copy_r_ready),
    .i_destination_done           (destination_cmd_done_q),
    .i_destination_cmdblock_params(csr_reg2hw.dst_cmdblock_params),
    .i_patch_mode                 (csr_reg2hw.patch_mode),
    .i_patch_table                (csr_reg2hw.patch_table),
    .o_read_request_busy          (csr_hw2reg.status_busy.copy_read_request.d),
    .o_axi_read_busy              (csr_hw2reg.status_busy.copy_axi_read.d),
    .o_address_patching_busy      (csr_hw2reg.status_busy.copy_address_patching.d),
    .o_fill_counters_busy         (csr_hw2reg.status_busy.copy_fill_counters.d),
    .o_write_request_busy         (csr_hw2reg.status_busy.copy_axi_write_request.d),
    .o_command_stalled            (command_stalled),
    .o_must_be_stalled            (must_be_stalled),
    .o_fill_count                 (fill_count),
    .o_errors                     (copy_errors),
    .o_instruction_index          (copy_instruction_index),
    .i_ram_impl                   (i_copy_ram_impl),
    .o_ram_impl                   (o_copy_ram_impl)
  );

  for (genvar destination_index = 0; unsigned'(destination_index) < NumDestinations; destination_index++) begin : gen_obs_fill
    assign csr_hw2reg.status_fill_counter[destination_index].is_stalled.d  = command_stalled;
    assign csr_hw2reg.status_fill_counter[destination_index].would_stall.d = must_be_stalled[destination_index];
    assign csr_hw2reg.status_fill_counter[destination_index].count.d       = fill_count[destination_index];
  end

  assign csr_hw2reg.irq_status.copy_data_misaligned.de          = copy_errors.copy_data_misaligned;
  assign csr_hw2reg.irq_status.copy_fill_counter_done_pop.de    = copy_errors.fill_counter_done_pop;
  assign csr_hw2reg.irq_status.copy_fill_counter_overflow.de    = copy_errors.fill_counter_overflow;
  assign csr_hw2reg.irq_status.copy_axi_read_resp_slverr.de     = copy_errors.axi_read_response_slverr;
  assign csr_hw2reg.irq_status.copy_axi_read_resp_decerr.de     = copy_errors.axi_read_response_decerr;
  assign csr_hw2reg.irq_status.copy_axi_write_resp_slverr.de    = copy_errors.axi_write_response_slverr;
  assign csr_hw2reg.irq_status.copy_axi_write_resp_decerr.de    = copy_errors.axi_write_response_decerr;

  /////////////////////////
  // AXI Manager Merging //
  /////////////////////////
  aic_cd_axi_merge #(
    .AxiIdWidth  (AxiManIdWidth),
    .AxiIdForCopy(AxiIdForCopy),
    .CutAw       (CutAxiManAw),
    .CutW        (CutAxiManW),
    .CutB        (CutAxiManB),
    .CutAr       (CutAxiManAr),
    .CutR        (CutAxiManR),
    .axi_aw_t    (axi_m_aw_t),
    .axi_w_t     (axi_m_w_t),
    .axi_b_t     (axi_m_b_t),
    .axi_ar_t    (axi_m_ar_t),
    .axi_r_t     (axi_m_r_t)
  ) u_aic_cd_axi_merge (
    .i_clk,
    .i_rst_n,
    .i_axi_instruction_ar      (axi_instruction_ar),
    .i_axi_instruction_ar_valid(axi_instruction_ar_valid),
    .o_axi_instruction_ar_ready(axi_instruction_ar_ready),
    .o_axi_instruction_r       (axi_instruction_r),
    .o_axi_instruction_r_valid (axi_instruction_r_valid),
    .i_axi_instruction_r_ready (axi_instruction_r_ready),
    .i_axi_copy_aw             (axi_copy_aw),
    .i_axi_copy_aw_valid       (axi_copy_aw_valid),
    .o_axi_copy_aw_ready       (axi_copy_aw_ready),
    .i_axi_copy_w              (axi_copy_w),
    .i_axi_copy_w_valid        (axi_copy_w_valid),
    .o_axi_copy_w_ready        (axi_copy_w_ready),
    .o_axi_copy_b              (axi_copy_b),
    .o_axi_copy_b_valid        (axi_copy_b_valid),
    .i_axi_copy_b_ready        (axi_copy_b_ready),
    .i_axi_copy_ar             (axi_copy_ar),
    .i_axi_copy_ar_valid       (axi_copy_ar_valid),
    .o_axi_copy_ar_ready       (axi_copy_ar_ready),
    .o_axi_copy_r              (axi_copy_r),
    .o_axi_copy_r_valid        (axi_copy_r_valid),
    .i_axi_copy_r_ready        (axi_copy_r_ready),
    .o_axi_m_aw,
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    .o_axi_m_w,
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    .i_axi_m_b,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,
    .o_axi_m_ar,
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    .i_axi_m_r,
    .i_axi_m_r_valid,
    .o_axi_m_r_ready
  );

  ////////////////////////
  // Interrupt Requests //
  ////////////////////////

  // Combine all IRQs to a single IRQ
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) o_irq <= 1'b0;
    else          o_irq <= |(csr_reg2hw.irq_status & csr_reg2hw.irq_en);
  end

  // Hardcode the status to high, enables are connected close to module that produces them
  assign csr_hw2reg.irq_status.task_list_done.d                = 1'b1;

  assign csr_hw2reg.irq_status.command_dropped.d               = 1'b1;
  assign csr_hw2reg.irq_status.command_empty_task_list.d       = 1'b1;

  assign csr_hw2reg.irq_status.instr_axi_resp_slverr.d         = 1'b1;
  assign csr_hw2reg.irq_status.instr_axi_resp_decerr.d         = 1'b1;
  assign csr_hw2reg.irq_status.instr_dst_id_mapping.d          = 1'b1;
  assign csr_hw2reg.irq_status.instr_patch_mode_mapping.d      = 1'b1;
  assign csr_hw2reg.irq_status.instr_patch_id_0_mapping.d      = 1'b1;
  assign csr_hw2reg.irq_status.instr_patch_id_1_mapping.d      = 1'b1;
  assign csr_hw2reg.irq_status.instr_token_illegal_opcode.d    = 1'b1;
  assign csr_hw2reg.irq_status.instr_token_local_map_empty.d   = 1'b1;
  assign csr_hw2reg.irq_status.instr_token_global_map_empty.d  = 1'b1;
  assign csr_hw2reg.irq_status.instr_token_local_mapping.d     = 1'b1;
  assign csr_hw2reg.irq_status.instr_token_global_mapping.d    = 1'b1;

  assign csr_hw2reg.irq_status.copy_data_misaligned.d          = 1'b1;
  assign csr_hw2reg.irq_status.copy_fill_counter_done_pop.d    = 1'b1;
  assign csr_hw2reg.irq_status.copy_fill_counter_overflow.d    = 1'b1;
  assign csr_hw2reg.irq_status.copy_axi_read_resp_slverr.d     = 1'b1;
  assign csr_hw2reg.irq_status.copy_axi_read_resp_decerr.d     = 1'b1;
  assign csr_hw2reg.irq_status.copy_axi_write_resp_slverr.d    = 1'b1;
  assign csr_hw2reg.irq_status.copy_axi_write_resp_decerr.d    = 1'b1;

  assign csr_hw2reg.irq_status.dbg_sw_interrupt.d              = 1'b1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  // If single ports of one of the subblocks it is hooked up directly
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.de = csr_reg2hw.command_control.dbg_sw_irq.q;

  // Error Cause
  logic       error_cause_is_set;
  always_comb error_cause_is_set = |csr_reg2hw.error_cause.q;

  aic_cd_pkg::task_list_word_length_t selected_error_cause;
  always_comb begin
    if      (|copy_errors)                  selected_error_cause = copy_instruction_index;
    else if (|error_instruction_validation) selected_error_cause = instruction_index;
    else                                    selected_error_cause = aic_cd_pkg::task_list_word_length_t'(0);
  end
  assign csr_hw2reg.error_cause.d  = selected_error_cause;

  assign csr_hw2reg.error_cause.de = ~error_cause_is_set & (
      (|copy_errors)
    | (|error_instruction_validation)
  );

  // If in copy an error occurs, do not process further instructions
  always_comb drop_instructions = |copy_errors;

endmodule
