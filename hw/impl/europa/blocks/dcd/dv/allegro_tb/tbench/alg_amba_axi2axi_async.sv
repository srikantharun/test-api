module alg_amba_axi2axi_async #(parameter AXI_DATA_WIDTH=128)
(
  input logic          r_clk            ,
  input logic          r_rstn           ,
  output logic [63:0]  r_araddr         ,
  output logic [1:0]   r_arburst        ,
  output logic [4:0]   r_arid           ,
  output logic [7:0]   r_arlen          ,
  input  logic         r_arready        ,
  output logic [2:0]   r_arsize         ,
  output logic         r_arvalid        ,
  output logic [63:0]  r_awaddr         ,
  output logic [1:0]   r_awburst        ,
  output logic [4:0]   r_awid           ,
  output logic [7:0]   r_awlen          ,
  input  logic         r_awready        ,
  output logic [2:0]   r_awsize         ,
  output logic         r_awvalid        ,
  output logic         r_bready         ,
  input  logic         r_bvalid         ,
  input  logic [1:0]   r_bresp          ,
  input  logic [4:0]   r_bid            ,
  input  logic [AXI_DATA_WIDTH-1:0] r_rdata,
  input  logic [4:0]   r_rid            ,
  input  logic         r_rlast          ,
  output logic         r_rready         ,
  input  logic         r_rvalid         ,
  input  logic [1:0]   r_rresp          ,
  output logic [AXI_DATA_WIDTH-1:0] r_wdata,
  output logic [(AXI_DATA_WIDTH/8)-1:0]  r_wstrb,
  output logic         r_wlast          ,
  input  logic         r_wready         ,
  output logic         r_wvalid         ,
  input logic          w_clk            ,
  input logic          w_rstn           ,
  input  logic [63:0]  w_araddr         ,
  input  logic [1:0]   w_arburst        ,
  input  logic [4:0]   w_arid           ,
  input  logic [7:0]   w_arlen          ,
  output logic         w_arready        ,
  input  logic [2:0]   w_arsize         ,
  input  logic         w_arvalid        ,
  input  logic [63:0]  w_awaddr         ,
  input  logic [1:0]   w_awburst        ,
  input  logic [4:0]   w_awid           ,
  input  logic [7:0]   w_awlen          ,
  output logic         w_awready        ,
  input  logic [2:0]   w_awsize         ,
  input  logic         w_awvalid        ,
  input  logic         w_bready         ,
  output logic         w_bvalid         ,
  output logic [1:0]   w_bresp          ,
  output logic [4:0]   w_bid            ,
  output logic [AXI_DATA_WIDTH-1:0] w_rdata,
  output logic [4:0]   w_rid            ,
  output logic         w_rlast          ,
  input  logic         w_rready         ,
  output logic         w_rvalid         ,
  output logic [1:0]   w_rresp          ,
  input  logic [AXI_DATA_WIDTH-1:0] w_wdata,
  input  logic [(AXI_DATA_WIDTH/8)-1:0]  w_wstrb,
  input  logic         w_wlast          ,
  output logic         w_wready         ,
  input  logic         w_wvalid
);

localparam AR_SIZE=64+2+5+8+3;
logic [AR_SIZE-1:0] ardatain;
logic [AR_SIZE-1:0] ardataout;
assign ardatain = {w_araddr,w_arburst,w_arid,w_arlen,w_arsize};
alg_amba_fifo_async #(.DATA_WIDTH(AR_SIZE)) I_ARSYNC (
  .wr_rstn      (w_rstn),
  .wr_clk       (w_clk),
  .wr_data      (ardatain),
  .wr_valid     (w_arvalid),
  .wr_ready     (w_arready),
  .rd_rstn      (r_rstn),
  .rd_clk       (r_clk),
  .rd_data      (ardataout),
  .rd_valid     (r_arvalid),
  .rd_ready     (r_arready)
);
assign {r_araddr,r_arburst,r_arid,r_arlen,r_arsize} = ardataout;


localparam R_SIZE=5+2+AXI_DATA_WIDTH+1;
logic [R_SIZE-1:0] rdatain;
logic [R_SIZE-1:0] rdataout;
assign rdataout = {r_rid,r_rresp,r_rdata,r_rlast};
alg_amba_fifo_async #(.DATA_WIDTH(R_SIZE)) I_RSYNC (
  .wr_rstn      (r_rstn),
  .wr_clk       (r_clk),
  .wr_data      (rdataout),
  .wr_valid     (r_rvalid),
  .wr_ready     (r_rready),
  .rd_rstn      (w_rstn),
  .rd_clk       (w_clk),
  .rd_data      (rdatain),
  .rd_valid     (w_rvalid),
  .rd_ready     (w_rready)
);
assign {w_rid,w_rresp,w_rdata,w_rlast} = rdatain;


localparam AW_SIZE=64+2+5+8+3;
logic [AW_SIZE-1:0] awdatain;
logic [AW_SIZE-1:0] awdataout;
assign awdatain = {w_awaddr,w_awburst,w_awid,w_awlen,w_awsize};
alg_amba_fifo_async #(.DATA_WIDTH(AW_SIZE)) I_AWSYNC (
  .wr_rstn      (w_rstn),
  .wr_clk       (w_clk),
  .wr_data      (awdatain),
  .wr_valid     (w_awvalid),
  .wr_ready     (w_awready),
  .rd_rstn      (r_rstn),
  .rd_clk       (r_clk),
  .rd_data      (awdataout),
  .rd_valid     (r_awvalid),
  .rd_ready     (r_awready)
);
assign {r_awaddr,r_awburst,r_awid,r_awlen,r_awsize} = awdataout;


localparam W_SIZE=AXI_DATA_WIDTH+(AXI_DATA_WIDTH/8)+1;
logic [W_SIZE-1:0] wdatain;
logic [W_SIZE-1:0] wdataout;
assign wdatain = {w_wdata,w_wstrb,w_wlast};
alg_amba_fifo_async #(.DATA_WIDTH(W_SIZE)) I_WSYNC (
  .wr_rstn      (w_rstn),
  .wr_clk       (w_clk),
  .wr_data      (wdatain),
  .wr_valid     (w_wvalid),
  .wr_ready     (w_wready),
  .rd_rstn      (r_rstn),
  .rd_clk       (r_clk),
  .rd_data      (wdataout),
  .rd_valid     (r_wvalid),
  .rd_ready     (r_wready)
);
assign {r_wdata,r_wstrb,r_wlast} = wdataout;


localparam B_SIZE=5+2;
logic [B_SIZE-1:0] bdatain;
logic [B_SIZE-1:0] bdataout;
assign bdataout = {r_bid,r_bresp};
alg_amba_fifo_async #(.DATA_WIDTH(B_SIZE)) I_BSYNC (
  .wr_rstn      (r_rstn),
  .wr_clk       (r_clk),
  .wr_data      (bdataout),
  .wr_valid     (r_bvalid),
  .wr_ready     (r_bready),
  .rd_rstn      (w_rstn),
  .rd_clk       (w_clk),
  .rd_data      (bdatain),
  .rd_valid     (w_bvalid),
  .rd_ready     (w_bready)
);
assign {w_bid,w_bresp} = bdatain;

endmodule
