
module alg_amba_vip_pipe #(
  parameter PIPE_ENABLE = 1,
  parameter DATA_WIDTH  = 128
)(
  al_vip_axi_if.slavemod               s_axi,
  al_vip_axi_if.mastermod              m_axi
);

localparam DATA_WIDTH_AR = 82;
localparam DATA_WIDTH_AW = 82;
localparam DATA_WIDTH_B  = 7;
localparam DATA_WIDTH_R  = DATA_WIDTH+8;
localparam DATA_WIDTH_W  = DATA_WIDTH+(DATA_WIDTH/8)+1;

logic [DATA_WIDTH_AR-1:0] in_data_ar;
logic [DATA_WIDTH_AW-1:0] in_data_aw;
logic [DATA_WIDTH_B-1:0]  in_data_b;
logic [DATA_WIDTH_R-1:0]  in_data_r;
logic [DATA_WIDTH_W-1:0]  in_data_w;

logic [DATA_WIDTH_AR-1:0] out_data_ar;
logic [DATA_WIDTH_AW-1:0] out_data_aw;
logic [DATA_WIDTH_B-1:0]  out_data_b;
logic [DATA_WIDTH_R-1:0]  out_data_r;
logic [DATA_WIDTH_W-1:0]  out_data_w;

/**************** AR *************************/

assign in_data_ar     = {s_axi.araddr, s_axi.arburst, s_axi.arid, s_axi.arlen, s_axi.arsize};
assign m_axi.araddr   = out_data_ar[81:18];
assign m_axi.arburst  = out_data_ar[17:16];
assign m_axi.arid     = out_data_ar[15:11];
assign m_axi.arlen    = out_data_ar[10:3];
assign m_axi.arsize   = out_data_ar[2:0];

alg_amba_vip_base_vldrdy_pipe #(
  .RSTPOL     (0),
  .NO_PIPE    (1-PIPE_ENABLE),
  .DATA_WIDTH (DATA_WIDTH_AR)
) PIPE_AR (
  .rstn       (s_axi.rstn),
  .clk        (s_axi.clk),
  .in_valid   (s_axi.arvalid),
  .in_data    (in_data_ar),
  .in_ready   (s_axi.arready),
  .out_valid  (m_axi.arvalid),
  .out_data   (out_data_ar),
  .out_ready  (m_axi.arready)
);

/**************** AW *************************/

assign in_data_aw     = {s_axi.awaddr, s_axi.awburst, s_axi.awid, s_axi.awlen, s_axi.awsize};
assign m_axi.awaddr   = out_data_aw[81:18];
assign m_axi.awburst  = out_data_aw[17:16];
assign m_axi.awid     = out_data_aw[15:11];
assign m_axi.awlen    = out_data_aw[10:3];
assign m_axi.awsize   = out_data_aw[2:0];

alg_amba_vip_base_vldrdy_pipe #(
  .RSTPOL     (0),
  .NO_PIPE    (1-PIPE_ENABLE),
  .DATA_WIDTH (DATA_WIDTH_AW)
) PIPE_AW (
  .rstn       (s_axi.rstn),
  .clk        (s_axi.clk),
  .in_valid   (s_axi.awvalid),
  .in_data    (in_data_aw),
  .in_ready   (s_axi.awready),
  .out_valid  (m_axi.awvalid),
  .out_data   (out_data_aw),
  .out_ready  (m_axi.awready)
);

/**************** B **************************/

assign in_data_b   = {m_axi.bresp, m_axi.bid};
assign s_axi.bresp = out_data_b[6:5];
assign s_axi.bid   = out_data_b[4:0];

alg_amba_vip_base_vldrdy_pipe #(
  .RSTPOL     (0),
  .NO_PIPE    (1-PIPE_ENABLE),
  .DATA_WIDTH (DATA_WIDTH_B)
) PIPE_B (
  .rstn       (s_axi.rstn),
  .clk        (s_axi.clk),
  .in_valid   (m_axi.bvalid),
  .in_data    (in_data_b),
  .in_ready   (m_axi.bready),
  .out_valid  (s_axi.bvalid),
  .out_data   (out_data_b),
  .out_ready  (s_axi.bready)
);

/**************** R **************************/

assign in_data_r   = {m_axi.rdata, m_axi.rid, m_axi.rlast, m_axi.rresp};
assign s_axi.rdata = out_data_r[DATA_WIDTH_R-1:8];
assign s_axi.rid   = out_data_r[7:3];
assign s_axi.rlast = out_data_r[2];
assign s_axi.rresp = out_data_r[1:0];

alg_amba_vip_base_vldrdy_pipe #(
  .RSTPOL     (0),
  .NO_PIPE    (1-PIPE_ENABLE),
  .DATA_WIDTH (DATA_WIDTH_R)
) PIPE_R (
  .rstn       (s_axi.rstn),
  .clk        (s_axi.clk),
  .in_valid   (m_axi.rvalid),
  .in_data    (in_data_r),
  .in_ready   (m_axi.rready),
  .out_valid  (s_axi.rvalid),
  .out_data   (out_data_r),
  .out_ready  (s_axi.rready)
);

/**************** W **************************/

assign in_data_w   = {s_axi.wdata, s_axi.wstrb, s_axi.wlast};
assign m_axi.wdata = out_data_w[DATA_WIDTH_W-1:(DATA_WIDTH/8)+1];
assign m_axi.wstrb = out_data_w[(DATA_WIDTH/8):1];
assign m_axi.wlast = out_data_w[0];

alg_amba_vip_base_vldrdy_pipe #(
  .RSTPOL     (0),
  .NO_PIPE    (1-PIPE_ENABLE),
  .DATA_WIDTH (DATA_WIDTH_W)
) PIPE_W (
  .rstn       (s_axi.rstn),
  .clk        (s_axi.clk),
  .in_valid   (s_axi.wvalid),
  .in_data    (in_data_w),
  .in_ready   (s_axi.wready),
  .out_valid  (m_axi.wvalid),
  .out_data   (out_data_w),
  .out_ready  (m_axi.wready)
);

endmodule
