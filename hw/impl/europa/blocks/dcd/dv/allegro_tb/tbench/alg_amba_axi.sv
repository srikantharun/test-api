



interface Axi_if #(parameter BUS_WIDTH = 128)  (
  input logic clk,
  input logic rstn
);

  logic [63:0]  araddr;
  logic [1:0]   arburst;
  logic [4:0]   arid;
  logic [7:0]   arlen;
  logic         arready;
  logic [2:0]   arsize;
  logic         arvalid;
  logic [63:0]  awaddr;
  logic [1:0]   awburst;
  logic [4:0]   awid;
  logic [7:0]   awlen;
  logic         awready;
  logic [2:0]   awsize;
  logic         awvalid;
  logic         bready;
  logic         bvalid;
  logic [1:0]   bresp;
  logic [4:0]   bid;
  logic [BUS_WIDTH-1:0] rdata;
  logic [4:0]   rid;
  logic         rlast;
  logic         rready;
  logic         rvalid;
  logic [1:0]   rresp;
  logic [BUS_WIDTH-1:0] wdata;
  logic [(BUS_WIDTH/8)-1:0]  wstrb;
  logic         wlast;
  logic         wready;
  logic         wvalid;

  logic [2 :0]  bus_id;
  logic [15:0]  currentframe;
  int file;
  logic [4 :0]  buffid;
  logic time_stamp;
  string filename;
  logic [5:0] fifo_awid[31:0];
  logic       fifo_wreq;
  logic       fifo_wren;
  logic       fifo_rden;
  logic       fifo_rreq;
  logic [5:0] wptr;
  logic [5:0] rptr;
  logic       i_wr_full;
  logic       i_rd_empty;

  assign fifo_wreq  = (awvalid && awready);
  assign fifo_rreq  = (wvalid && wready && wlast);
  assign i_rd_empty = (wptr == rptr);
  assign i_wr_full  = ((rptr[5] != wptr[5]) && (rptr[4:0] == wptr[4:0]));
  assign fifo_wren  = (fifo_wreq && !i_wr_full);
  assign fifo_rden  = (fifo_rreq && !i_rd_empty);
  assign buffid     = fifo_awid[rptr[4:0]];

  always @ (posedge clk) begin
    if (rstn == 0) begin
      rptr <= '0;
      wptr <= '0;
      for(int i=0;i<32;i++)
        fifo_awid[i] <= '0;
    end else begin
      if (fifo_wren == 1) begin
        wptr                 <= wptr + 1;
        fifo_awid[wptr[4:0]] <= awid;
      end
      if (fifo_rden == 1) begin
        rptr <= rptr + 1;
      end
    end
  end

  always (*xprop_off*) @(posedge clk) begin
    if (i_wr_full == 1) begin $fatal(1,"AXI error : write awid fifo full"); end
  end


  
  task trace();
    string mytime;
    forever begin
      @(posedge clk);
      if (time_stamp==0) mytime = "";
      if (time_stamp==1) mytime = $sformatf(" %0d", $stime);
      if (awvalid == 1 && awready == 1) begin
        file = open(currentframe,bus_id,awid,"aw");
        $fdisplay(file, "%h %h %h %h %h%s", awid, awaddr, awlen, awsize, awburst, mytime);
        $fclose(file);
      end
      if (wvalid == 1 && wready == 1) begin
        file = open(currentframe,bus_id,buffid,"dw");
        $fdisplay(file, "%h %h%s", wdata, wlast, mytime);
        $fclose(file);
      end
      if (bvalid == 1 && bready == 1) begin
        file = open(currentframe,bus_id,bid,"rw");
        $fdisplay(file, "%h%s", bid, mytime);
        $fclose(file);
      end
      if (arvalid == 1 && arready == 1) begin
        file = open(currentframe,bus_id,arid,"ar");
        $fdisplay(file, "%h %h %h %h %h%s", arid, araddr, arlen, arsize, arburst, mytime);
        $fclose(file);
      end
      if (rvalid == 1 && rready == 1) begin
        file = open(currentframe,bus_id,rid,"dr");
        $fdisplay(file, "%h %h %h%s", rid, rdata, rlast, mytime);
        $fclose(file);
      end
    end
  endtask

  function int open(logic[15:0] currentframe, logic[2:0] bus_id, logic [4:0] id, string channel);
    int open_file;
    string open_filename;
    open_filename = {"SimAxi",$sformatf("%0d",int'(bus_id)),"_ID_",$sformatf("%02h",int'(id)),"_",$sformatf("%04h",int'(currentframe)),"_",channel,".hex"};
    open_file = $fopen(open_filename, "a+");
    if (!open_file) begin
      $fatal(1, "Error writing file %s for writing", open_filename);
    end
    return open_file;
  endfunction


  modport mastermod (
    input  clk,
    input  rstn,
    output araddr,
    output arburst,
    output arid,
    output arlen,
    input  arready,
    output arsize,
    output arvalid,
    output awaddr,
    output awburst,
    output awid,
    output awlen,
    input  awready,
    output awsize,
    output awvalid,
    output bready,
    input  bvalid,
    input  bresp,
    input  bid,
    input  rdata,
    input  rid,
    input  rlast,
    output rready,
    input  rvalid,
    input  rresp,
    output wdata,
    output wstrb,
    output wlast,
    input  wready,
    output wvalid
  );

  modport slavemod (
    input  clk,
    input  rstn,
    input  araddr,
    input  arburst,
    input  arid,
    input  arlen,
    output arready,
    input  arsize,
    input  arvalid,
    input  awaddr,
    input  awburst,
    input  awid,
    input  awlen,
    output awready,
    input  awsize,
    input  awvalid,
    input  bready,
    output bvalid,
    output bresp,
    output bid,
    output rdata,
    output rid,
    output rlast,
    input  rready,
    output rvalid,
    output rresp,
    input  wdata,
    input  wstrb,
    input  wlast,
    output wready,
    input  wvalid
  );

endinterface

package AxiPkg;

  class Axi;
    virtual Axi_if axi_bus[7];

    function new(virtual Axi_if axi_bus[7]);
      this.axi_bus = axi_bus;
    endfunction

  endclass
endpackage
