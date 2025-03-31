// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger for the AI Core
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TIMESTAMP_LOGGER_AIC_SV
`define TIMESTAMP_LOGGER_AIC_SV

module timestamp_logger_aic #(
  parameter int unsigned AxiSIdWidth  = 4,
  parameter int unsigned AxiMIdWidth  = 4,
  parameter int unsigned AxiAddrWidth = 36,
  parameter int unsigned AxiDataWidth = 64,

  /// Implementation input type for the sram
  parameter type sram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Implementation output type for the sram
  parameter type sram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,

  /// Start address regions for CSR, and MEM:
  parameter longint REGION_ST_ADDR[2] = {40'h0, 40'h4000},
  /// End address regions for CSR, and MEM:
  parameter longint REGION_END_ADDR[2] = {40'hfff, 40'h7fff},

  localparam type axi_s_id_t = logic[AxiSIdWidth     -1:0],
  localparam type axi_m_id_t = logic[AxiMIdWidth     -1:0],
  localparam type axi_addr_t = logic[AxiAddrWidth    -1:0],
  localparam type axi_data_t = logic[AxiDataWidth    -1:0],
  localparam type axi_strb_t = logic[(AxiDataWidth/8)-1:0]
) (
  input  wire   i_clk,
  input  wire   i_rst_n,

  input  logic  i_scan_en,

  input  logic  i_sync_start,

  input  logic  i_m_ifd0_st,
  input  logic  i_m_ifd1_st,
  input  logic  i_m_ifd2_st,
  input  logic  i_m_ifdw_st,
  input  logic  i_d_ifd0_st,
  input  logic  i_d_ifd1_st,
  input  logic  i_m_odr_st,
  input  logic  i_d_odr_st,
  input  logic  i_mid_mvmexe_st,
  input  logic  i_mid_mvmprg_st,
  input  logic  i_mid_iau_st,
  input  logic  i_mid_dpu_st,
  input  logic  i_did_dwpu_st,
  input  logic  i_did_iau_st,
  input  logic  i_did_dpu_st,
  input  logic  i_dma_ch0_st,
  input  logic  i_dma_ch1_st,

  input  logic  i_m_ifd0_end,
  input  logic  i_m_ifd1_end,
  input  logic  i_m_ifd2_end,
  input  logic  i_m_ifdw_end,
  input  logic  i_d_ifd0_end,
  input  logic  i_d_ifd1_end,
  input  logic  i_m_odr_end,
  input  logic  i_d_odr_end,
  input  logic  i_mid_mvmexe_end,
  input  logic  i_mid_mvmprg_end,
  input  logic  i_mid_iau_end,
  input  logic  i_mid_dpu_end,
  input  logic  i_did_dwpu_end,
  input  logic  i_did_iau_end,
  input  logic  i_did_dpu_end,
  input  logic  i_dma_ch0_end,
  input  logic  i_dma_ch1_end,

  input  logic  i_acd_trigger,
  input  logic [timestamp_logger_aic_pkg::TimeLogACDMsgW-1:0] i_acd_message,

  // PC tracing:
  input  logic i_pc_0_valid,
  input  logic [timestamp_logger_aic_csr_reg_pkg::PLEN-2:0] i_pc_0,
  input  logic i_pc_1_valid,
  input  logic [timestamp_logger_aic_csr_reg_pkg::PLEN-2:0] i_pc_1,

  // Store tracing:
  input  logic i_st_valid,
  input  logic [timestamp_logger_aic_csr_reg_pkg::AW-1:0] i_st_addr,
  // Load tracing:
  input  logic i_ld_valid,
  input  logic [timestamp_logger_aic_csr_reg_pkg::AW-1:0] i_ld_addr,

  ///// AXI subordinate:
  // Write Address Channel
  input  axi_s_id_t           i_axi_s_aw_id,
  input  axi_addr_t           i_axi_s_aw_addr,
  input  axi_pkg::axi_len_t   i_axi_s_aw_len,
  input  axi_pkg::axi_size_t  i_axi_s_aw_size,
  input  axi_pkg::axi_burst_t i_axi_s_aw_burst,
  input  logic                i_axi_s_aw_valid,
  output logic                o_axi_s_aw_ready,
  // Write  Data Channel
  input  axi_data_t           i_axi_s_w_data,
  input  axi_strb_t           i_axi_s_w_strb,
  input  logic                i_axi_s_w_last,
  input  logic                i_axi_s_w_valid,
  output logic                o_axi_s_w_ready,
  // Write Response Channel
  output axi_s_id_t           o_axi_s_b_id,
  output axi_pkg::axi_resp_t  o_axi_s_b_resp,
  output logic                o_axi_s_b_valid,
  input  logic                i_axi_s_b_ready,
  // Read Address Channel
  input  axi_s_id_t           i_axi_s_ar_id,
  input  axi_addr_t           i_axi_s_ar_addr,
  input  axi_pkg::axi_len_t   i_axi_s_ar_len,
  input  axi_pkg::axi_size_t  i_axi_s_ar_size,
  input  axi_pkg::axi_burst_t i_axi_s_ar_burst,
  input  logic                i_axi_s_ar_valid,
  output logic                o_axi_s_ar_ready,
  // Read Data Channel
  output axi_s_id_t           o_axi_s_r_id,
  output axi_data_t           o_axi_s_r_data,
  output axi_pkg::axi_resp_t  o_axi_s_r_resp,
  output logic                o_axi_s_r_last,
  output logic                o_axi_s_r_valid,
  input  logic                i_axi_s_r_ready,

  ///// AXI manager:
  // Write Address Channel
  output axi_m_id_t           o_axi_m_aw_id,
  output axi_addr_t           o_axi_m_aw_addr,
  output axi_pkg::axi_len_t   o_axi_m_aw_len,
  output axi_pkg::axi_size_t  o_axi_m_aw_size,
  output axi_pkg::axi_burst_t o_axi_m_aw_burst,
  output logic                o_axi_m_aw_valid,
  input  logic                i_axi_m_aw_ready,
  // Write  Data Channel
  output axi_data_t           o_axi_m_w_data,
  output axi_strb_t           o_axi_m_w_strb,
  output logic                o_axi_m_w_last,
  output logic                o_axi_m_w_valid,
  input  logic                i_axi_m_w_ready,
  // Write Response Channel
  input  axi_m_id_t           i_axi_m_b_id,
  input  axi_pkg::axi_resp_t  i_axi_m_b_resp,
  input  logic                i_axi_m_b_valid,
  output logic                o_axi_m_b_ready,
  // Read Address Channel
  output axi_m_id_t           o_axi_m_ar_id,
  output axi_addr_t           o_axi_m_ar_addr,
  output axi_pkg::axi_len_t   o_axi_m_ar_len,
  output axi_pkg::axi_size_t  o_axi_m_ar_size,
  output axi_pkg::axi_burst_t o_axi_m_ar_burst,
  output logic                o_axi_m_ar_valid,
  input  logic                i_axi_m_ar_ready,
  // Read Data Channel
  input  axi_m_id_t           i_axi_m_r_id,
  input  axi_data_t           i_axi_m_r_data,
  input  axi_pkg::axi_resp_t  i_axi_m_r_resp,
  input  logic                i_axi_m_r_last,
  input  logic                i_axi_m_r_valid,
  output logic                o_axi_m_r_ready,

  ///// SRAM Sideband Signals
  input  sram_impl_inp_t      i_sram_impl,
  output sram_impl_oup_t      o_sram_impl
);

  timestamp_logger_aic_csr_reg_pkg::timestamp_logger_aic_csr_reg2hw_t csr_reg2hw;
  timestamp_logger_csr_reg_pkg::apb_h2d_t ip_csr_req;
  timestamp_logger_csr_reg_pkg::apb_d2h_t ip_csr_rsp;

  timestamp_logger_aic_csr_reg_pkg::timestamp_logger_aic_csr_reg2hw_dp_dev_mask_reg_t dev_st, dev_end;
  timestamp_logger_aic_csr_reg_pkg::timestamp_logger_aic_csr_reg2hw_dp_dev_mask_reg_t masked_dev_st, masked_dev_end;
  logic [timestamp_logger_aic_csr_reg_pkg::PC_COMPARES-1:0] pc_triggers;
  logic [timestamp_logger_aic_csr_reg_pkg::ST_COMPARES-1:0] st_triggers;
  logic [timestamp_logger_aic_csr_reg_pkg::LD_COMPARES-1:0] ld_triggers;

  logic [timestamp_logger_aic_pkg::TimeLogNumGroups-1:0] triggers;
  logic [timestamp_logger_aic_pkg::TimeLogNumGroups-1:0] [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] messages;

  always_comb masked_dev_st  = csr_reg2hw.dp_dev_mask & dev_st;
  always_comb masked_dev_end = csr_reg2hw.dp_dev_mask & dev_end;
  always_comb dev_st = timestamp_logger_aic_csr_reg_pkg::timestamp_logger_aic_csr_reg2hw_dp_dev_mask_reg_t'{
    m_ifd0:     i_m_ifd0_st,
    m_ifd1:     i_m_ifd1_st,
    m_ifd2:     i_m_ifd2_st,
    m_ifdw:     i_m_ifdw_st,
    d_ifd0:     i_d_ifd0_st,
    d_ifd1:     i_d_ifd1_st,
    m_odr:      i_m_odr_st,
    d_odr:      i_d_odr_st,
    mid_mvmexe: i_mid_mvmexe_st,
    mid_mvmprg: i_mid_mvmprg_st,
    mid_iau:    i_mid_iau_st,
    mid_dpu:    i_mid_dpu_st,
    did_dwpu:   i_did_dwpu_st,
    did_iau:    i_did_iau_st,
    did_dpu:    i_did_dpu_st,
    dma_ch0:    i_dma_ch0_st,
    dma_ch1:    i_dma_ch1_st
  };

  always_comb dev_end = timestamp_logger_aic_csr_reg_pkg::timestamp_logger_aic_csr_reg2hw_dp_dev_mask_reg_t'{
    m_ifd0:     i_m_ifd0_end,
    m_ifd1:     i_m_ifd1_end,
    m_ifd2:     i_m_ifd2_end,
    m_ifdw:     i_m_ifdw_end,
    d_ifd0:     i_d_ifd0_end,
    d_ifd1:     i_d_ifd1_end,
    m_odr:      i_m_odr_end,
    d_odr:      i_d_odr_end,
    mid_mvmexe: i_mid_mvmexe_end,
    mid_mvmprg: i_mid_mvmprg_end,
    mid_iau:    i_mid_iau_end,
    mid_dpu:    i_mid_dpu_end,
    did_dwpu:   i_did_dwpu_end,
    did_iau:    i_did_iau_end,
    did_dpu:    i_did_dpu_end,
    dma_ch0:    i_dma_ch0_end,
    dma_ch1:    i_dma_ch1_end
  };

  always_comb begin
    triggers[timestamp_logger_aic_pkg::swep_idx]    = csr_reg2hw.swep.qe;
    triggers[timestamp_logger_aic_pkg::acd_idx]     = i_acd_trigger;
    triggers[timestamp_logger_aic_pkg::dev_st_idx]  = |masked_dev_st;
    triggers[timestamp_logger_aic_pkg::dev_end_idx] = |masked_dev_end;
    triggers[timestamp_logger_aic_pkg::pc_idx]      = |pc_triggers;
    triggers[timestamp_logger_aic_pkg::st_idx]      = |st_triggers;
    triggers[timestamp_logger_aic_pkg::ld_idx]      = |ld_triggers;

    messages[timestamp_logger_aic_pkg::swep_idx]    = csr_reg2hw.swep.q;
    messages[timestamp_logger_aic_pkg::acd_idx]     = i_acd_message;
    messages[timestamp_logger_aic_pkg::dev_st_idx]  = masked_dev_st;
    messages[timestamp_logger_aic_pkg::dev_end_idx] = masked_dev_end;
    messages[timestamp_logger_aic_pkg::pc_idx]      = pc_triggers;
    messages[timestamp_logger_aic_pkg::st_idx]      = st_triggers;
    messages[timestamp_logger_aic_pkg::ld_idx]      = ld_triggers;
  end

  // PC compare:
  always_comb begin
    pc_triggers = 0;
    for (int unsigned i = 0; i<timestamp_logger_aic_csr_reg_pkg::PC_COMPARES; i++) begin
      pc_triggers[i] = (i_pc_0_valid & (i_pc_0 == csr_reg2hw.pc_compare[i])) ||
                       (i_pc_1_valid & (i_pc_1 == csr_reg2hw.pc_compare[i]));
    end
  end

  // ST compare:
  always_comb begin
    st_triggers = 0;
    for (int unsigned i = 0; i<timestamp_logger_aic_csr_reg_pkg::ST_COMPARES; i++) begin
      st_triggers[i] = i_st_valid & ((i_st_addr >= csr_reg2hw.st_trace_low[i]) &&
                                     (i_st_addr <  csr_reg2hw.st_trace_high[i]));
    end
  end

  // LD compare:
  always_comb begin
    ld_triggers = 0;
    for (int unsigned i = 0; i<timestamp_logger_aic_csr_reg_pkg::LD_COMPARES; i++) begin
      ld_triggers[i] = i_ld_valid & ((i_ld_addr >= csr_reg2hw.ld_trace_low[i]) &&
                                     (i_ld_addr <  csr_reg2hw.ld_trace_high[i]));
    end
  end

  timestamp_logger #(
    .NumGroups(timestamp_logger_aic_pkg::TimeLogNumGroups),

    .AxiSIdWidth(AxiSIdWidth),
    .AxiMIdWidth(AxiMIdWidth),
    .AxiAddrWidth(AxiAddrWidth),
    .AxiDataWidth(AxiDataWidth),

    .GroupMsgWidth(timestamp_logger_aic_pkg::TimeLogGroupMsgWidth),
    .GroupFifoDepth(timestamp_logger_aic_pkg::TimeLogGroupFifoDepth),

    .TimestampFifoDepth(timestamp_logger_aic_pkg::TimeLogTimestampFifoDepth),

    /// Implementation input type for the sram
    .sram_impl_inp_t(sram_impl_inp_t),
    /// Implementation output type for the sram
    .sram_impl_oup_t(sram_impl_oup_t),

    .MemDepth(timestamp_logger_aic_pkg::TimeLogMemDepth),

    .UseMacro(timestamp_logger_aic_pkg::TimeLogUseMacro),
    .SramImplKey(timestamp_logger_aic_pkg::TimeLogSramImplKey),

    // default address regions for CSR, and MEM:
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR)
  ) u_timestamp_logger (
    .i_clk,
    .i_rst_n,

    .i_scan_en,

    .i_group_trigger(triggers),
    .i_group_message(messages),

    .i_sync_start,

    ///// AXI subordinate:
    // Write Address Channel
    .i_axi_s_aw_id,
    .i_axi_s_aw_addr,
    .i_axi_s_aw_len,
    .i_axi_s_aw_size,
    .i_axi_s_aw_burst,
    .i_axi_s_aw_valid,
    .o_axi_s_aw_ready,
    // Write  Data Channel
    .i_axi_s_w_data,
    .i_axi_s_w_strb,
    .i_axi_s_w_last,
    .i_axi_s_w_valid,
    .o_axi_s_w_ready,
    // Write Response Channel
    .o_axi_s_b_id,
    .o_axi_s_b_resp,
    .o_axi_s_b_valid,
    .i_axi_s_b_ready,
    // Read Address Channel
    .i_axi_s_ar_id,
    .i_axi_s_ar_addr,
    .i_axi_s_ar_len,
    .i_axi_s_ar_size,
    .i_axi_s_ar_burst,
    .i_axi_s_ar_valid,
    .o_axi_s_ar_ready,
    // Read Data Channel
    .o_axi_s_r_id,
    .o_axi_s_r_data,
    .o_axi_s_r_resp,
    .o_axi_s_r_last,
    .o_axi_s_r_valid,
    .i_axi_s_r_ready,

    ///// AXI manager:
    // Write Address Channel
    .o_axi_m_aw_id,
    .o_axi_m_aw_addr,
    .o_axi_m_aw_len,
    .o_axi_m_aw_size,
    .o_axi_m_aw_burst,
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    // Write  Data Channel
    .o_axi_m_w_data,
    .o_axi_m_w_strb,
    .o_axi_m_w_last,
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    // Write Response Channel
    .i_axi_m_b_id,
    .i_axi_m_b_resp,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,
    // Read Address Channel
    .o_axi_m_ar_id,
    .o_axi_m_ar_addr,
    .o_axi_m_ar_len,
    .o_axi_m_ar_size,
    .o_axi_m_ar_burst,
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    // Read Data Channel
    .i_axi_m_r_id,
    .i_axi_m_r_data,
    .i_axi_m_r_resp,
    .i_axi_m_r_last,
    .i_axi_m_r_valid,
    .o_axi_m_r_ready,

    // IP specific CSR connection:
    .o_ip_csr_req(ip_csr_req),
    .i_ip_csr_rsp(ip_csr_rsp),

    ///// SRAM Sideband Signals
    .i_sram_impl,
    .o_sram_impl
  );

  timestamp_logger_aic_csr_reg_top u_ip_csr (
    .clk_i(i_clk),
    .rst_ni(i_rst_n),
    .apb_i(ip_csr_req),
    .apb_o(ip_csr_rsp),
    // To HW
    .reg2hw(csr_reg2hw),
    // Config
    .devmode_i(1'b1)
  );
endmodule

`endif  // TIMESTAMP_LOGGER_AIC_SV
