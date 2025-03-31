// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger for the SDMA
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module timestamp_logger_sdma #(
  parameter int unsigned AxiSIdWidth  = 4,
  parameter int unsigned AxiMIdWidth  = 4,
  parameter int unsigned AxiAddrWidth = 36,
  parameter int unsigned AxiDataWidth = 64,

  // default address regions for CSR, and MEM:
  parameter longint REGION_ST_ADDR[2] = {40'h0, 40'h4000},
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

  input  logic  [timestamp_logger_sdma_pkg::TimeLogNumDevs-1:0 ] i_ts_start,
  input  logic  [timestamp_logger_sdma_pkg::TimeLogNumDevs-1:0 ] i_ts_end,

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
  output logic                o_axi_m_r_ready
);

  timestamp_logger_sdma_csr_reg_pkg::timestamp_logger_sdma_csr_reg2hw_t csr_reg2hw;
  timestamp_logger_csr_reg_pkg::apb_h2d_t ip_csr_req;
  timestamp_logger_csr_reg_pkg::apb_d2h_t ip_csr_rsp;

  timestamp_logger_sdma_csr_reg_pkg::timestamp_logger_sdma_csr_reg2hw_channel_mask_reg_t masked_dev_st, masked_dev_end;

  logic [timestamp_logger_sdma_pkg::TimeLogNumGroups-1:0] triggers;
  logic [timestamp_logger_sdma_pkg::TimeLogNumGroups-1:0] [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] messages;

  always_comb masked_dev_st  = csr_reg2hw.channel_mask & i_ts_start;
  always_comb masked_dev_end = csr_reg2hw.channel_mask & i_ts_end;

  always_comb begin
    triggers[timestamp_logger_sdma_pkg::swep_idx]    = csr_reg2hw.swep.qe;
    triggers[timestamp_logger_sdma_pkg::dev_st_idx]  = |masked_dev_st;
    triggers[timestamp_logger_sdma_pkg::dev_end_idx] = |masked_dev_end;

    messages[timestamp_logger_sdma_pkg::swep_idx]    = csr_reg2hw.swep.q;
    messages[timestamp_logger_sdma_pkg::dev_st_idx]  = masked_dev_st;
    messages[timestamp_logger_sdma_pkg::dev_end_idx] = masked_dev_end;
  end

  timestamp_logger #(
    .NumGroups(timestamp_logger_sdma_pkg::TimeLogNumGroups),

    .AxiSIdWidth(AxiSIdWidth),
    .AxiMIdWidth(AxiMIdWidth),
    .AxiAddrWidth(AxiAddrWidth),
    .AxiDataWidth(AxiDataWidth),

    .GroupMsgWidth(timestamp_logger_sdma_pkg::TimeLogGroupMsgWidth),
    .GroupFifoDepth(timestamp_logger_sdma_pkg::TimeLogGroupFifoDepth),

    .TimestampFifoDepth(timestamp_logger_sdma_pkg::TimeLogTimestampFifoDepth),

    .MemDepth(timestamp_logger_sdma_pkg::TimeLogMemDepth),
    .UseMacro(timestamp_logger_sdma_pkg::TimeLogUseMacro),

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
    .i_sram_impl('{default:0}),
    .o_sram_impl()  // ASO-UNUSED_OUTPUT: port not used
  );

  timestamp_logger_sdma_csr_reg_top u_ip_csr (
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

