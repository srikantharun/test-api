// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Multistage wrapper around PVE AXI channels using
// cc_stream_spill_reg.
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

module pve_axi_multistage_spill_reg
  import axi_pkg::*;
#(
  parameter int unsigned NUM_STAGES_AW = 1,
  parameter int unsigned NUM_STAGES_W = 1,
  parameter int unsigned NUM_STAGES_B = 1,
  parameter int unsigned NUM_STAGES_AR = 1,
  parameter int unsigned NUM_STAGES_R = 1,
  parameter type axi_addr_t = logic [39:0],
  parameter type axi_id_t   = logic [ 3:0],
  parameter type axi_data_t = logic [63:0],
  parameter type axi_strb_t = logic [ 7:0]
) (
  // Clock and reset signals
  input  wire        i_clk,
  input  wire        i_rst_n,
  // Subordinate side
  // AXI write address channel
  input  logic       i_axi_s_awvalid,
  input  axi_id_t    i_axi_s_awid,
  input  axi_addr_t  i_axi_s_awaddr,
  input  axi_len_t   i_axi_s_awlen,
  input  axi_size_e  i_axi_s_awsize,
  input  axi_burst_e i_axi_s_awburst,
  input  logic       i_axi_s_awlock,
  input  axi_cache_e i_axi_s_awcache,
  input  axi_prot_t  i_axi_s_awprot,
  input  axi_atop_t  i_axi_s_awatop,
  output logic       o_axi_s_awready,
  // AXI write data channel
  input  logic       i_axi_s_wvalid,
  input  axi_data_t  i_axi_s_wdata,
  input  axi_strb_t  i_axi_s_wstrb,
  input  logic       i_axi_s_wlast,
  output logic       o_axi_s_wready,
  // AXI write response channel
  output logic       o_axi_s_bvalid,
  output axi_id_t    o_axi_s_bid,
  output axi_resp_e  o_axi_s_bresp,
  input  logic       i_axi_s_bready,
  // AXI read address channel
  input  logic       i_axi_s_arvalid,
  input  axi_id_t    i_axi_s_arid,
  input  axi_addr_t  i_axi_s_araddr,
  input  axi_len_t   i_axi_s_arlen,
  input  axi_size_e  i_axi_s_arsize,
  input  axi_burst_e i_axi_s_arburst,
  input  logic       i_axi_s_arlock,
  input  axi_cache_e i_axi_s_arcache,
  input  axi_prot_t  i_axi_s_arprot,
  output logic       o_axi_s_arready,
  // AXI read data/response channel
  output logic       o_axi_s_rvalid,
  output axi_id_t    o_axi_s_rid,
  output axi_data_t  o_axi_s_rdata,
  output axi_resp_e  o_axi_s_rresp,
  output logic       o_axi_s_rlast,
  input  logic       i_axi_s_rready,
  // Manager Ports
  // AXI write address channel
  output logic       o_axi_m_awvalid,
  output axi_id_t    o_axi_m_awid,
  output axi_addr_t  o_axi_m_awaddr,
  output axi_len_t   o_axi_m_awlen,
  output axi_size_e  o_axi_m_awsize,
  output axi_burst_e o_axi_m_awburst,
  output logic       o_axi_m_awlock,
  output axi_cache_e o_axi_m_awcache,
  output axi_prot_t  o_axi_m_awprot,
  output axi_atop_t  o_axi_m_awatop,
  input  logic       i_axi_m_awready,
  // AXI write data channel
  output logic       o_axi_m_wvalid,
  output axi_data_t  o_axi_m_wdata,
  output axi_strb_t  o_axi_m_wstrb,
  output logic       o_axi_m_wlast,
  input  logic       i_axi_m_wready,
  // AXI write response channel
  input  logic       i_axi_m_bvalid,
  input  axi_id_t    i_axi_m_bid,
  input  axi_resp_e  i_axi_m_bresp,
  output logic       o_axi_m_bready,
  // AXI read address channel
  output logic       o_axi_m_arvalid,
  output axi_id_t    o_axi_m_arid,
  output axi_addr_t  o_axi_m_araddr,
  output axi_len_t   o_axi_m_arlen,
  output axi_size_e  o_axi_m_arsize,
  output axi_burst_e o_axi_m_arburst,
  output logic       o_axi_m_arlock,
  output axi_cache_e o_axi_m_arcache,
  output axi_prot_t  o_axi_m_arprot,
  input  logic       i_axi_m_arready,
  // AXI read data/response channel
  input  logic       i_axi_m_rvalid,
  input  axi_id_t    i_axi_m_rid,
  input  axi_data_t  i_axi_m_rdata,
  input  axi_resp_e  i_axi_m_rresp,
  input  logic       i_axi_m_rlast,
  output logic       o_axi_m_rready
);

  // AXI types
  typedef struct packed {
    axi_id_t    id;
    axi_addr_t  addr;
    axi_len_t   len;
    axi_size_e  size;
    axi_burst_e burst;
    logic       lock;
    axi_cache_e cache;
    axi_prot_t  prot;
    axi_atop_t  atop;
  } axi_aw_t;

  typedef struct packed {
    axi_data_t  data;
    axi_strb_t  strb;
    logic       last;
  } axi_w_t;

  typedef struct packed {
    axi_id_t   id;
    axi_resp_e resp;
  } axi_b_t;

  typedef struct packed {
    axi_id_t    id;
    axi_addr_t  addr;
    axi_len_t   len;
    axi_size_e  size;
    axi_burst_e burst;
    logic       lock;
    axi_cache_e cache;
    axi_prot_t  prot;
  } axi_ar_t;

  typedef struct packed {
    axi_id_t   id;
    axi_data_t data;
    axi_resp_e resp;
    logic      last;
  } axi_r_t;

  localparam int unsigned LOC_NUM_STAGES_AW = (NUM_STAGES_AW == 0) ? 1 : NUM_STAGES_AW;
  localparam int unsigned LOC_NUM_STAGES_W  = (NUM_STAGES_W  == 0) ? 1 : NUM_STAGES_W;
  localparam int unsigned LOC_NUM_STAGES_B  = (NUM_STAGES_B  == 0) ? 1 : NUM_STAGES_B;
  localparam int unsigned LOC_NUM_STAGES_AR = (NUM_STAGES_AR == 0) ? 1 : NUM_STAGES_AR;
  localparam int unsigned LOC_NUM_STAGES_R  = (NUM_STAGES_R  == 0) ? 1 : NUM_STAGES_R;
  localparam bit BYPASS_AW = (NUM_STAGES_AW == 0) ? 1'b1 : 1'b0;
  localparam bit BYPASS_W  = (NUM_STAGES_W  == 0) ? 1'b1 : 1'b0;
  localparam bit BYPASS_B  = (NUM_STAGES_B  == 0) ? 1'b1 : 1'b0;
  localparam bit BYPASS_AR = (NUM_STAGES_AR == 0) ? 1'b1 : 1'b0;
  localparam bit BYPASS_R  = (NUM_STAGES_R  == 0) ? 1'b1 : 1'b0;

  axi_aw_t axi_aw      [LOC_NUM_STAGES_AW+1];
  logic    axi_aw_valid[LOC_NUM_STAGES_AW+1];
  logic    axi_aw_ready[LOC_NUM_STAGES_AW+1];
  axi_w_t  axi_w       [LOC_NUM_STAGES_W+1];
  logic    axi_w_valid [LOC_NUM_STAGES_W+1];
  logic    axi_w_ready [LOC_NUM_STAGES_W+1];
  axi_b_t  axi_b       [LOC_NUM_STAGES_B+1];
  logic    axi_b_valid [LOC_NUM_STAGES_B+1];
  logic    axi_b_ready [LOC_NUM_STAGES_B+1];
  axi_ar_t axi_ar      [LOC_NUM_STAGES_AR+1];
  logic    axi_ar_valid[LOC_NUM_STAGES_AR+1];
  logic    axi_ar_ready[LOC_NUM_STAGES_AR+1];
  axi_r_t  axi_r       [LOC_NUM_STAGES_R+1];
  logic    axi_r_valid [LOC_NUM_STAGES_R+1];
  logic    axi_r_ready [LOC_NUM_STAGES_R+1];

  // AW channel
  always_comb axi_aw[0]       = '{ id    : i_axi_s_awid,
                                   addr  : i_axi_s_awaddr,
                                   len   : i_axi_s_awlen,
                                   size  : i_axi_s_awsize,
                                   burst : i_axi_s_awburst,
                                   lock  : i_axi_s_awlock,
                                   cache : i_axi_s_awcache,
                                   prot  : i_axi_s_awprot,
                                   atop  : i_axi_s_awatop };
  always_comb axi_aw_valid[0] = i_axi_s_awvalid;
  always_comb o_axi_s_awready = axi_aw_ready[0];
  for (genvar i = 0; i < LOC_NUM_STAGES_AW; i = i + 1) begin : g_aw_stages
    cc_stream_spill_reg #(
      .data_t(axi_aw_t),
      .Bypass(BYPASS_AW)
    ) u_spill_reg_aw (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (axi_aw[i]),
      .i_valid(axi_aw_valid[i]),
      .o_ready(axi_aw_ready[i]),
      .o_data (axi_aw[i+1]),
      .o_valid(axi_aw_valid[i+1]),
      .i_ready(axi_aw_ready[i+1])
    );
  end: g_aw_stages
  always_comb o_axi_m_awid                    = axi_aw[LOC_NUM_STAGES_AW].id;
  always_comb o_axi_m_awaddr                  = axi_aw[LOC_NUM_STAGES_AW].addr;
  always_comb o_axi_m_awlen                   = axi_aw[LOC_NUM_STAGES_AW].len;
  always_comb o_axi_m_awsize                  = axi_aw[LOC_NUM_STAGES_AW].size;
  always_comb o_axi_m_awburst                 = axi_aw[LOC_NUM_STAGES_AW].burst;
  always_comb o_axi_m_awlock                  = axi_aw[LOC_NUM_STAGES_AW].lock;
  always_comb o_axi_m_awcache                 = axi_aw[LOC_NUM_STAGES_AW].cache;
  always_comb o_axi_m_awprot                  = axi_aw[LOC_NUM_STAGES_AW].prot;
  always_comb o_axi_m_awatop                  = axi_aw[LOC_NUM_STAGES_AW].atop;
  always_comb o_axi_m_awvalid                 = axi_aw_valid[LOC_NUM_STAGES_AW];
  always_comb axi_aw_ready[LOC_NUM_STAGES_AW] = i_axi_m_awready;

  // W channel
  always_comb axi_w[0]       = '{ data : i_axi_s_wdata,
                                  strb : i_axi_s_wstrb,
                                  last : i_axi_s_wlast };
  always_comb axi_w_valid[0] = i_axi_s_wvalid;
  always_comb o_axi_s_wready = axi_w_ready[0];
  for (genvar i = 0; i < LOC_NUM_STAGES_W; i = i + 1) begin : g_w_stages
    cc_stream_spill_reg #(
      .data_t(axi_w_t),
      .Bypass(BYPASS_W)
    ) u_spill_reg_w (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (axi_w[i]),
      .i_valid(axi_w_valid[i]),
      .o_ready(axi_w_ready[i]),
      .o_data (axi_w[i+1]),
      .o_valid(axi_w_valid[i+1]),
      .i_ready(axi_w_ready[i+1])
    );
  end: g_w_stages
  always_comb o_axi_m_wdata                 = axi_w[LOC_NUM_STAGES_W].data;
  always_comb o_axi_m_wstrb                 = axi_w[LOC_NUM_STAGES_W].strb;
  always_comb o_axi_m_wlast                 = axi_w[LOC_NUM_STAGES_W].last;
  always_comb o_axi_m_wvalid                = axi_w_valid[LOC_NUM_STAGES_W];
  always_comb axi_w_ready[LOC_NUM_STAGES_W] = i_axi_m_wready;

  // B channel
  always_comb axi_b[0]       = '{ id   : i_axi_m_bid,
                                  resp : i_axi_m_bresp };
  always_comb axi_b_valid[0] = i_axi_m_bvalid;
  always_comb o_axi_m_bready = axi_b_ready[0];
  for (genvar i = 0; i < LOC_NUM_STAGES_B; i = i + 1) begin : g_b_stages
    cc_stream_spill_reg #(
      .data_t(axi_b_t),
      .Bypass(BYPASS_B)
    ) u_spill_reg_b (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (axi_b[i]),
      .i_valid(axi_b_valid[i]),
      .o_ready(axi_b_ready[i]),
      .o_data (axi_b[i+1]),
      .o_valid(axi_b_valid[i+1]),
      .i_ready(axi_b_ready[i+1])
    );
  end: g_b_stages
  always_comb o_axi_s_bid                   = axi_b[LOC_NUM_STAGES_B].id;
  always_comb o_axi_s_bresp                 = axi_b[LOC_NUM_STAGES_B].resp;
  always_comb o_axi_s_bvalid                = axi_b_valid[LOC_NUM_STAGES_B];
  always_comb axi_b_ready[LOC_NUM_STAGES_B] = i_axi_s_bready;

  // AR channel
  always_comb axi_ar[0]       = '{ id    : i_axi_s_arid,
                                   addr  : i_axi_s_araddr,
                                   len   : i_axi_s_arlen,
                                   size  : i_axi_s_arsize,
                                   burst : i_axi_s_arburst,
                                   lock  : i_axi_s_arlock,
                                   cache : i_axi_s_arcache,
                                   prot  : i_axi_s_arprot };
  always_comb axi_ar_valid[0] = i_axi_s_arvalid;
  always_comb o_axi_s_arready = axi_ar_ready[0];
  for (genvar i = 0; i < LOC_NUM_STAGES_AR; i = i + 1) begin : g_ar_stages
    cc_stream_spill_reg #(
      .data_t(axi_ar_t),
      .Bypass(BYPASS_AR)
    ) u_spill_reg_ar (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (axi_ar[i]),
      .i_valid(axi_ar_valid[i]),
      .o_ready(axi_ar_ready[i]),
      .o_data (axi_ar[i+1]),
      .o_valid(axi_ar_valid[i+1]),
      .i_ready(axi_ar_ready[i+1])
    );
  end: g_ar_stages
  always_comb o_axi_m_arid                    = axi_ar[LOC_NUM_STAGES_AR].id;
  always_comb o_axi_m_araddr                  = axi_ar[LOC_NUM_STAGES_AR].addr;
  always_comb o_axi_m_arlen                   = axi_ar[LOC_NUM_STAGES_AR].len;
  always_comb o_axi_m_arsize                  = axi_ar[LOC_NUM_STAGES_AR].size;
  always_comb o_axi_m_arburst                 = axi_ar[LOC_NUM_STAGES_AR].burst;
  always_comb o_axi_m_arlock                  = axi_ar[LOC_NUM_STAGES_AR].lock;
  always_comb o_axi_m_arcache                 = axi_ar[LOC_NUM_STAGES_AR].cache;
  always_comb o_axi_m_arprot                  = axi_ar[LOC_NUM_STAGES_AR].prot;
  always_comb o_axi_m_arvalid                 = axi_ar_valid[LOC_NUM_STAGES_AR];
  always_comb axi_ar_ready[LOC_NUM_STAGES_AR] = i_axi_m_arready;

  // R channel
  always_comb axi_r[0]       = '{ id   : i_axi_m_rid,
                                  data : i_axi_m_rdata,
                                  resp : i_axi_m_rresp,
                                  last : i_axi_m_rlast };
  always_comb axi_r_valid[0] = i_axi_m_rvalid;
  always_comb o_axi_m_rready = axi_r_ready[0];
  for (genvar i = 0; i < LOC_NUM_STAGES_R; i = i + 1) begin : g_r_stages
    cc_stream_spill_reg #(
      .data_t(axi_r_t),
      .Bypass(BYPASS_R)
    ) u_spill_reg_r (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (axi_r[i]),
      .i_valid(axi_r_valid[i]),
      .o_ready(axi_r_ready[i]),
      .o_data (axi_r[i+1]),
      .o_valid(axi_r_valid[i+1]),
      .i_ready(axi_r_ready[i+1])
    );
  end: g_r_stages
  always_comb o_axi_s_rid                   = axi_r[LOC_NUM_STAGES_R].id;
  always_comb o_axi_s_rdata                 = axi_r[LOC_NUM_STAGES_R].data;
  always_comb o_axi_s_rresp                 = axi_r[LOC_NUM_STAGES_R].resp;
  always_comb o_axi_s_rlast                 = axi_r[LOC_NUM_STAGES_R].last;
  always_comb o_axi_s_rvalid                = axi_r_valid[LOC_NUM_STAGES_R];
  always_comb axi_r_ready[LOC_NUM_STAGES_R] = i_axi_s_rready;

endmodule
