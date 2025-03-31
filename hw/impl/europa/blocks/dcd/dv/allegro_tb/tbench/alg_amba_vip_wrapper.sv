





module alg_amba_vip_wrapper #(
  parameter DATA_WIDTH = 128,
  parameter ID         = 1,
  parameter APB_RESYNC = 0,
  parameter ID_START   = 0,
  parameter ID_END     = 63,
  parameter DELAYLINE_OUTSTANDING_LOG2 = 8
) (
  
  input  logic                         pclk,
  input  logic                         presetn,
  input  logic                         psel,
  input  logic                         penable,
  input  logic                         pwrite,
  input  logic [15:0]                  paddr,
  input  logic [31:0]                  pwdata,
  output logic [31:0]                  prdata,
  output logic                         pready,
  output logic                         pslverr,
  output logic                         pintreq,
  
  output logic [31:0]                  ip_ctrl_write,
  input  logic [31:0]                  ip_ctrl_read,
  input  logic                         axi_pc_asserted,
  input  logic [96:0]                  axi_pc_status,
  
  input  logic                         aclk,
  input  logic                         aresetn,
  
  output logic [63:0]                  axi_araddr,
  output logic [1:0]                   axi_arburst,
  output logic [4:0]                   axi_arid,
  output logic [7:0]                   axi_arlen,
  input  logic                         axi_arready,
  output logic [2:0]                   axi_arsize,
  output logic                         axi_arvalid,
  output logic [63:0]                  axi_awaddr,
  output logic [1:0]                   axi_awburst,
  output logic [4:0]                   axi_awid,
  output logic [7:0]                   axi_awlen,
  input  logic                         axi_awready,
  output logic [2:0]                   axi_awsize,
  output logic                         axi_awvalid,
  output logic                         axi_bready,
  input  logic                         axi_bvalid,
  input  logic                         axi_bresp,
  input  logic [4:0]                   axi_bid,
  input  logic [DATA_WIDTH-1:0]        axi_rdata,
  input  logic [4:0]                   axi_rid,
  input  logic                         axi_rlast,
  output logic                         axi_rready,
  input  logic                         axi_rvalid,
  input  logic                         axi_rresp,
  output logic [DATA_WIDTH-1:0]        axi_wdata,
  output logic [(DATA_WIDTH/8)-1:0]    axi_wstrb,
  output logic                         axi_wlast,
  input  logic                         axi_wready,
  output logic                         axi_wvalid,
  
  input  logic [63:0]                  ip_araddr,
  input  logic [1:0]                   ip_arburst,
  input  logic [4:0]                   ip_arid,
  input  logic [7:0]                   ip_arlen,
  output logic                         ip_arready,
  input  logic [2:0]                   ip_arsize,
  input  logic                         ip_arvalid,
  input  logic [63:0]                  ip_awaddr,
  input  logic [1:0]                   ip_awburst,
  input  logic [4:0]                   ip_awid,
  input  logic [7:0]                   ip_awlen,
  output logic                         ip_awready,
  input  logic [2:0]                   ip_awsize,
  input  logic                         ip_awvalid,
  input  logic                         ip_bready,
  output logic                         ip_bvalid,
  output logic                         ip_bresp,
  output logic [4:0]                   ip_bid,
  output logic [DATA_WIDTH-1:0]        ip_rdata,
  output logic [4:0]                   ip_rid,
  output logic                         ip_rlast,
  input  logic                         ip_rready,
  output logic                         ip_rvalid,
  output logic                         ip_rresp,
  input  logic [DATA_WIDTH-1:0]        ip_wdata,
  input  logic [(DATA_WIDTH/8)-1:0]    ip_wstrb,
  input  logic                         ip_wlast,
  output logic                         ip_wready,
  input  logic                         ip_wvalid
);

al_vip_apb_if  #(.ADDR(16))          apb   (.clk(pclk), .rstn(presetn));
al_vip_axi_if  #(.WIDTH(DATA_WIDTH)) s_axi (.clk(aclk), .rstn(aresetn));
al_vip_axi_if  #(.WIDTH(DATA_WIDTH)) m_axi (.clk(aclk), .rstn(aresetn));

assign apb.sel    = psel;
assign apb.enable = penable;
assign apb.write  = pwrite;
assign apb.addr   = paddr;
assign apb.wdata  = pwdata;
assign prdata      = apb.rdata;
assign pready      = apb.ready;
assign pslverr     = apb.slverr;

assign axi_araddr    = m_axi.araddr;
assign axi_arburst   = m_axi.arburst;
assign axi_arid      = m_axi.arid;
assign axi_arlen     = m_axi.arlen;
assign m_axi.arready = axi_arready;
assign axi_arsize    = m_axi.arsize;
assign axi_arvalid   = m_axi.arvalid;
assign axi_awaddr    = m_axi.awaddr;
assign axi_awburst   = m_axi.awburst;
assign axi_awid      = m_axi.awid;
assign axi_awlen     = m_axi.awlen;
assign m_axi.awready = axi_awready;
assign axi_awsize    = m_axi.awsize;
assign axi_awvalid   = m_axi.awvalid;
assign axi_bready    = m_axi.bready;
assign m_axi.bvalid  = axi_bvalid;
assign m_axi.bresp   = {axi_bresp, 1'b0};
assign m_axi.bid     = axi_bid;
assign m_axi.rdata   = axi_rdata;
assign m_axi.rid     = axi_rid;
assign m_axi.rlast   = axi_rlast;
assign axi_rready    = m_axi.rready;
assign m_axi.rvalid  = axi_rvalid;
assign m_axi.rresp   = {axi_rresp, 1'b0};
assign axi_wdata     = m_axi.wdata;
assign axi_wstrb     = m_axi.wstrb;
assign axi_wlast     = m_axi.wlast;
assign m_axi.wready  = axi_wready;
assign axi_wvalid    = m_axi.wvalid;

assign s_axi.araddr  = ip_araddr;
assign s_axi.arburst = ip_arburst;
assign s_axi.arid    = ip_arid;
assign s_axi.arlen   = ip_arlen;
assign ip_arready    = s_axi.arready;
assign s_axi.arsize  = ip_arsize;
assign s_axi.arvalid = ip_arvalid;
assign s_axi.awaddr  = ip_awaddr;
assign s_axi.awburst = ip_awburst;
assign s_axi.awid    = ip_awid;
assign s_axi.awlen   = ip_awlen;
assign ip_awready    = s_axi.awready;
assign s_axi.awsize  = ip_awsize;
assign s_axi.awvalid = ip_awvalid;
assign s_axi.bready  = ip_bready;
assign ip_bvalid     = s_axi.bvalid;
assign ip_bresp      = s_axi.bresp[1];
assign ip_bid        = s_axi.bid;
assign ip_rdata      = s_axi.rdata;
assign ip_rid        = s_axi.rid;
assign ip_rlast      = s_axi.rlast;
assign s_axi.rready  = ip_rready;
assign ip_rvalid     = s_axi.rvalid;
assign ip_rresp      = s_axi.rresp[1];
assign s_axi.wdata   = ip_wdata;
assign s_axi.wstrb   = ip_wstrb;
assign s_axi.wlast   = ip_wlast;
assign ip_wready     = s_axi.wready;
assign s_axi.wvalid  = ip_wvalid;

alg_amba_vip #(
  .DATA_WIDTH  (DATA_WIDTH),
  .ID          (ID),
  .APB_RESYNC  (APB_RESYNC),
  .ID_START    (ID_START),
  .ID_END      (ID_END),
  .DELAYLINE_OUTSTANDING_LOG2 (DELAYLINE_OUTSTANDING_LOG2)
) VIP (
  
  .irq         (pintreq),
  
  .apb         (apb),
  
  .s_axi       (s_axi),
  .m_axi       (m_axi),
  
  .user_output (ip_ctrl_write),
  .user_input  (ip_ctrl_read)
);

endmodule
