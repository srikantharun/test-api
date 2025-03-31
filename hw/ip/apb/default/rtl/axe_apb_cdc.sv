// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>


/// APB asynchronous bridge, handles CDC between APB interfaces on
/// asynchronous clock domains.
///
module axe_apb_cdc #(
  /// Number of synchronization stages
  parameter int unsigned SyncStages = 3,
  /// Width of the APB address (only used for typedef)
  parameter int unsigned ApbAddrWidth = 16,
  /// Width of the APB data (only used for typedef)
  parameter int unsigned ApbDataWidth = 32,
  /// Width of the APB strobe
  localparam int unsigned ApbStbWidth = ApbDataWidth / 8,
  /// APB address type
  parameter type  paddr_t = logic[ApbAddrWidth-1:0],
  /// APB data type
  parameter type  pdata_t = logic[ApbDataWidth-1:0],
  /// APB strobe type
  parameter type  pstrb_t = logic[ApbStbWidth-1:0]
)(
  /// Source domain clock, positive edge triggered
  input  wire                         i_src_clk,
  /// Source domain asynchronous reset, active low
  input  wire                         i_src_rst_n,
  /// Destination domain clock, positive edge triggered
  input  wire                         i_dst_clk,
  /// Destination domain asynchronous reset, active low
  input  wire                         i_dst_rst_n,
  /////////////////
  // Subordinate //
  /////////////////
  input  paddr_t                      i_apb_s_paddr,
  input  pdata_t                      i_apb_s_pwdata,
  input  logic                        i_apb_s_pwrite,
  input  logic                        i_apb_s_psel,
  input  logic                        i_apb_s_penable,
  input  pstrb_t                      i_apb_s_pstrb,
  input  axe_apb_pkg::apb_prot_t      i_apb_s_pprot,
  output logic                        o_apb_s_pready,
  output pdata_t                      o_apb_s_prdata,
  output logic                        o_apb_s_pslverr,
  /////////////
  // Manager //
  /////////////
  output paddr_t                      o_apb_m_paddr,
  output pdata_t                      o_apb_m_pwdata,
  output logic                        o_apb_m_pwrite,
  output logic                        o_apb_m_psel,
  output logic                        o_apb_m_penable,
  output pstrb_t                      o_apb_m_pstrb,
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot,
  input  logic                        i_apb_m_pready,
  input  pdata_t                      i_apb_m_prdata,
  input  logic                        i_apb_m_pslverr
);

  typedef struct packed {
    paddr_t                 paddr;
    pdata_t                 pwdata;
    logic                   pwrite;
    pstrb_t                 pstrb;
    axe_apb_pkg::apb_prot_t pprot;
  } apb_req_data_t;

  typedef struct packed {
    pdata_t prdata;
    logic   pslverr;
  } apb_resp_data_t;

  apb_req_data_t  apb_req_data,  apb_req_data_sync;
  apb_resp_data_t apb_resp_data, apb_resp_data_sync;

  logic apb_req_pulse, apb_req_pulse_sync;
  logic apb_resp_pulse, apb_resp_pulse_sync;

  logic apb_req_sync_busy;
  logic apb_resp_sync_busy;

  typedef enum logic {
    APB_SRC_IDLE,
    APB_SRC_BUSY
  } apb_src_state_e;

  typedef enum logic[1:0] {
    APB_DST_IDLE,
    APB_DST_REQ,
    APB_DST_BUSY
  } apb_dst_state_e;

  apb_src_state_e src_state_q, src_state_d;
  apb_dst_state_e dst_state_q, dst_state_d;

  logic src_state_change, dst_state_change;

  pdata_t                 apb_s_prdata_q;
  logic                   apb_s_pslverr_q;
  paddr_t                 apb_m_paddr_q;
  pdata_t                 apb_m_pwdata_q;
  logic                   apb_m_pwrite_q;
  pstrb_t                 apb_m_pstrb_q;
  axe_apb_pkg::apb_prot_t apb_m_pprot_q;

  // --------------------------------------------------------------------------
  // Source FSM
  // --------------------------------------------------------------------------

  always_comb begin
    o_apb_s_pready  = 1'b0;
    apb_req_pulse   = 1'b0;
    src_state_d     = src_state_q;

    unique case (src_state_q)
      APB_SRC_IDLE: begin
        if (i_apb_s_psel && i_apb_s_penable && !apb_req_sync_busy) begin
          src_state_d   = APB_SRC_BUSY;
          apb_req_pulse = 1'b1;
        end
      end
      APB_SRC_BUSY: begin
        if (apb_resp_pulse_sync) begin
          src_state_d    = APB_SRC_IDLE;
          o_apb_s_pready = 1'b1;
        end
      end
      default: /* Keep default values */;
    endcase
  end

  always_comb src_state_change = src_state_d != src_state_q;

  // DFFR: D-Flip-Flop, asynchronous reset.
  always_ff @(posedge i_src_clk or negedge i_src_rst_n) begin
    if (!i_src_rst_n)           src_state_q <= APB_SRC_IDLE;
    else if (src_state_change)  src_state_q <= src_state_d;
  end

  // --------------------------------------------------------------------------
  // Request synchronization
  // --------------------------------------------------------------------------

  always_comb apb_req_data.paddr  = i_apb_s_paddr;
  always_comb apb_req_data.pwdata = i_apb_s_pwdata;
  always_comb apb_req_data.pwrite = i_apb_s_pwrite;
  always_comb apb_req_data.pstrb  = i_apb_s_pstrb;
  always_comb apb_req_data.pprot  = i_apb_s_pprot;

  axe_ccl_cdc_bus # (
    .SyncStages   (SyncStages),
    .data_t       (apb_req_data_t)
  )
  u_apb_req_data_sync (
    .i_src_clk    (i_src_clk),
    .i_src_rst_n  (i_src_rst_n),
    .i_src_en     (apb_req_pulse),
    .i_src_data   (apb_req_data),
    .o_src_busy   (apb_req_sync_busy),
    .i_dst_clk    (i_dst_clk),
    .i_dst_rst_n  (i_dst_rst_n),
    .o_dst_data   (apb_req_data_sync),
    .o_dst_update (apb_req_pulse_sync)
  );

  // Output assignments.
  always_comb o_apb_m_paddr   = apb_req_data_sync.paddr;
  always_comb o_apb_m_pwdata  = apb_req_data_sync.pwdata;
  always_comb o_apb_m_pwrite  = apb_req_data_sync.pwrite;
  always_comb o_apb_m_pstrb   = apb_req_data_sync.pstrb;
  always_comb o_apb_m_pprot   = apb_req_data_sync.pprot;

  // --------------------------------------------------------------------------
  // Destination FSM
  // --------------------------------------------------------------------------

  always_comb begin
    o_apb_m_psel      = 1'b0;
    o_apb_m_penable   = 1'b0;
    apb_resp_pulse    = 1'b0;
    dst_state_d       = dst_state_q;

    unique case (dst_state_q)
      APB_DST_IDLE: begin
        if (apb_req_pulse_sync) begin
          if (!apb_resp_sync_busy) begin
            o_apb_m_psel  = 1'b1;
            dst_state_d   = APB_DST_BUSY;
          end else begin
            dst_state_d   = APB_DST_REQ;
          end
        end
      end
      APB_DST_REQ: begin
        if (!apb_resp_sync_busy) begin
          o_apb_m_psel  = 1'b1;
          dst_state_d   = APB_DST_BUSY;
        end
      end
      APB_DST_BUSY: begin
        o_apb_m_psel      = 1'b1;
        o_apb_m_penable   = 1'b1;
        if (i_apb_m_pready) begin
          dst_state_d     = APB_DST_IDLE;
          apb_resp_pulse  = 1'b1;
        end
      end
      default: /* Keep default values */;
    endcase
  end

  always_comb dst_state_change = dst_state_d != dst_state_q;

  // DFFR: D-Flip-Flop, asynchronous reset.
  always_ff @(posedge i_dst_clk or negedge i_dst_rst_n) begin
    if (!i_dst_rst_n)           dst_state_q <= APB_DST_IDLE;
    else if (dst_state_change)  dst_state_q <= dst_state_d;
  end

  // --------------------------------------------------------------------------
  // Response synchronization
  // --------------------------------------------------------------------------

  always_comb apb_resp_data.prdata  = i_apb_m_prdata;
  always_comb apb_resp_data.pslverr = i_apb_m_pslverr;

  axe_ccl_cdc_bus # (
    .SyncStages   (SyncStages),
    .data_t       (apb_resp_data_t)
  )
  u_apb_resp_data_sync (
    .i_src_clk    (i_dst_clk),
    .i_src_rst_n  (i_dst_rst_n),
    .i_src_en     (apb_resp_pulse),
    .i_src_data   (apb_resp_data),
    .o_src_busy   (apb_resp_sync_busy),
    .i_dst_clk    (i_src_clk),
    .i_dst_rst_n  (i_src_rst_n),
    .o_dst_data   (apb_resp_data_sync),
    .o_dst_update (apb_resp_pulse_sync)
  );

  always_comb o_apb_s_prdata  = apb_resp_data_sync.prdata;
  always_comb o_apb_s_pslverr = apb_resp_data_sync.pslverr;

endmodule
