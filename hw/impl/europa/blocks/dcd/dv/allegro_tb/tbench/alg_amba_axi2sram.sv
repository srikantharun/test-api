




module alg_amba_axi2sram #(parameter CHECK_ALIGN=1) (

  Axi_if.slavemod axi,
  Sram_if.mastermod  sram
);

  logic        write0    ;
  logic        bval0     ;
  logic        fw_rreq   ;
  logic        fw_rempty ;
  logic        fw_wfull  ;
  logic        fwa_wreq  ;
  logic        fwa_rreq  ;
  logic        fwa_rempty;
  logic        fwa_wfull ;
  logic [81:0] fwa_rdata ;
  logic [81:0] fwa_wdata ;
  logic [4:0]  id0       ;
  logic [63:0] waddr0    ;
  logic [63:0] winc      ;
  logic [63:0] wwrap     ;
  logic        read0     ;
  logic [63:0] raddr0    ;
  logic [63:0] araddr    ;
  logic [63:0] rinc      ;
  logic [63:0] rwrap     ;
  logic [7:0]  rcpt      ;
  logic [7:0]  arlen     ;
  logic [2:0]  arsize    ;
  logic [1:0]  arburst   ;
  logic [2:0]  wsize     ;
  logic [1:0]  wburst    ;
  logic        rlast0    ;
  logic        read      ;
  logic        rlast     ;
  logic [4:0]  rid       ;
  logic        fr_rreq   ;
  logic        fr_rempty ;
  logic        fr_wfull  ;
  logic [261:0]fr_rdata  ;
  logic [261:0]fr_wdata  ;
  logic        fra_wreq  ;
  logic        fra_rreq  ;
  logic        fra_rempty;
  logic        fra_wfull ;
  logic [81:0] fra_rdata ;
  logic [81:0] fra_wdata ;



  always  @ (posedge axi.clk )
  if (axi.rstn == 0) begin
    id0         <= 0;
    write0      <= 0;
    waddr0      <= 0;
    wsize       <= 0;
    wburst      <= 0;
    wwrap       <= 0;
  end else begin
    if (fwa_rempty == 0 && write0 == 0) begin
      waddr0      <= fwa_rdata[63:0];
      id0         <= fwa_rdata[76:72];
      wsize       <= fwa_rdata[79:77];
      wburst      <= fwa_rdata[81:80];
      write0      <= 1;
      if (fwa_rdata[81:80] == 2'b10) begin
        if(fwa_rdata[71:64] == 8'h01)
          wwrap       <= ((2**fwa_rdata[79:77]-1)<<1)|4'h1;
        else if(fwa_rdata[71:64] == 8'h03)
          wwrap       <= ((2**fwa_rdata[79:77]-1)<<2)|4'h3;
        else if(fwa_rdata[71:64] == 8'h07)
          wwrap       <= ((2**fwa_rdata[79:77]-1)<<3)|4'h7;
        else if(fwa_rdata[71:64] == 8'h0F)
          wwrap       <= ((2**fwa_rdata[79:77]-1)<<4)|4'hF;
        else begin
          $fatal(1,"AXI error: awlen value not supported for wrap access");
        end
      end
    end else if (axi.wvalid == 1 && write0 == 1) begin
      if (axi.wlast != 1) begin
        if (wburst == 2'b01) begin
          waddr0      <= winc;
        end else begin
          if (wburst == 2'b10) begin
            for(int i=0;i<64;i++)
              if(wwrap[i]==0)
                waddr0[i] <= waddr0[i];
              else
                waddr0[i] <= winc[i];
          end else begin
            if (wburst == 2'b00) begin
              waddr0      <= waddr0;
            end else begin
              $fatal(1,"AXI error: awburst value not supported");
            end
          end
        end
      end else begin
        write0      <= 0;
     end
   end
  end
  assign winc = waddr0 + (2**wsize);

  assign axi.wready  = write0;
  assign axi.awready = !fwa_wfull;
  assign fwa_wreq  = axi.awvalid && !fwa_wfull;
  assign fwa_rreq  = !write0;
  assign fwa_wdata[63:0]  = axi.awaddr;
  assign fwa_wdata[71:64] = axi.awlen;
  assign fwa_wdata[76:72] = axi.awid;
  assign fwa_wdata[79:77] = axi.awsize;
  assign fwa_wdata[81:80] = axi.awburst;

  assign sram.wdata  = axi.wdata   ;
  assign sram.wstrb  = axi.wstrb   ;
  assign sram.nwen   = !(axi.wvalid && write0) ;
  assign sram.waddr  = waddr0  ;

  assign bval0  = axi.wvalid && write0 && axi.wlast;
  assign axi.bvalid  = !fw_rempty;
  assign fw_rreq = !fw_rempty && axi.bready;


  alg_amba_fifo_fwft #(
    .FIFO_WIDTH           (82),
    .FIFO_LOG2_DEPTH      (12)
   ) fifo_write_outstanding (
    .clk                  (axi.clk),
    .rstn                 (axi.rstn),
    .wreq                 (fwa_wreq),
    .wdata                (fwa_wdata),
    .wfull                (fwa_wfull),
    .rreq                 (fwa_rreq),
    .rdata                (fwa_rdata),
    .rempty               (fwa_rempty)
   );


  alg_amba_fifo_fwft #(
    .FIFO_WIDTH           (5),
    .FIFO_LOG2_DEPTH      (12)
   ) fifo_write_response (
    .clk                  (axi.clk),
    .rstn                 (axi.rstn),
    .wreq                 (bval0),
    .wdata                (id0),
    .wfull                (fw_wfull),
    .rreq                 (fw_rreq),
    .rdata                (axi.bid),
    .rempty               (fw_rempty)
   );


  always (*xprop_off*) @(posedge axi.clk) begin
    if (fw_wfull == 1) begin $fatal(1,"AXI error: write response fifo full"); end
  end



  always  @ (posedge axi.clk )
  if (axi.rstn == 0) begin
    rid        <= '0;
    read       <= '0;
    rlast      <= '0;
    rcpt       <= '0;
    read0      <= '0;
    raddr0     <= '0;
  end else begin
    read       <= read0;
    rlast      <= rlast0;
    if (!fra_rempty && !read0) begin
      raddr0      <= araddr;
      read0       <= 1;
      rcpt        <= arlen;
      rid         <= fra_rdata[76:72];
    end else begin
      if (rcpt == 0) begin
        read0       <= 0;
      end else begin
        rcpt        <= rcpt - 1;
        if (arburst == 2'b01) begin
          raddr0      <= rinc;
        end else begin
          if (arburst == 2'b10) begin
            for(int i=0;i<64;i++)
              if(rwrap[i]==0)
                raddr0[i] <= araddr[i];
              else
                raddr0[i] <= rinc[i];
          end else begin
            if (arburst == 2'b00) begin
              raddr0      <= raddr0;
            end else begin
              $fatal(1,"AXI error: arburst value not supported");
            end
          end
        end
      end
    end
  end

  always @(arlen, arburst, arsize) begin
    if (arburst == 2'b10) begin
      if(arlen == 8'h01)
        rwrap     = ((2**arsize-1)<<1)|4'h1;
      else if(arlen == 8'h03)
        rwrap     = ((2**arsize-1)<<2)|4'h3;
      else if(arlen == 8'h07)
        rwrap     = ((2**arsize-1)<<3)|4'h7;
      else if(arlen == 8'h0F)
        rwrap     = ((2**arsize-1)<<4)|4'hF;
      else begin
        $fatal(1,"AXI error: arlen value not supported for wrap access");
      end
    end
  end

  assign rlast0  = read0 && (rcpt == 0);
  assign rinc    = raddr0 + (2**arsize);
  assign araddr  = fra_rdata[63:0];
  assign arlen   = fra_rdata[71:64];
  assign arsize  = fra_rdata[79:77];
  assign arburst = fra_rdata[81:80];

  assign fra_rreq  = rlast0;
  assign fra_wreq  = axi.arvalid && !fra_wfull;
  assign fra_wdata[63:0]  = axi.araddr;
  assign fra_wdata[71:64] = axi.arlen;
  assign fra_wdata[76:72] = axi.arid;
  assign fra_wdata[79:77] = axi.arsize;
  assign fra_wdata[81:80] = axi.arburst;
  assign fr_rreq   = !fr_rempty && axi.rready;

  assign axi.arready   = !fra_wfull;
  assign axi.rvalid    = !fr_rempty;
  assign axi.rdata     = fr_rdata[255:0];
  assign axi.rid       = fr_rdata[260:256];
  assign axi.rlast     = fr_rdata[261];

  assign fr_wdata[255:0]   = sram.rdata;
  assign fr_wdata[260:256] = rid ;
  assign fr_wdata[261]     = rlast;
  assign sram.nren         = !read0;
  assign sram.raddr        = raddr0;


  alg_amba_fifo_fwft #(
    .FIFO_WIDTH           (82),
    .FIFO_LOG2_DEPTH      (12)
   ) fifo_read_outstanding (
    .clk                  (axi.clk),
    .rstn                 (axi.rstn),
    .wreq                 (fra_wreq),
    .wdata                (fra_wdata),
    .wfull                (fra_wfull),
    .rreq                 (fra_rreq),
    .rdata                (fra_rdata),
    .rempty               (fra_rempty)
   );


  alg_amba_fifo_fwft #(
    .FIFO_WIDTH           (262),
    .FIFO_LOG2_DEPTH      (12)
   ) fifo_read_response (
    .clk                  (axi.clk),
    .rstn                 (axi.rstn),
    .wreq                 (read),
    .wdata                (fr_wdata),
    .wfull                (fr_wfull),
    .rreq                 (fr_rreq),
    .rdata                (fr_rdata),
    .rempty               (fr_rempty)
   );


  always (*xprop_off*) @(posedge axi.clk) begin
    if (fr_wfull == 1) begin $fatal(1,"AXI error: read response fifo full"); end
  end


always (*xprop_off*) @(posedge axi.clk) begin
  if(CHECK_ALIGN) begin
    if (axi.arvalid && axi.arready && axi.araddr[3:0] != 0) begin $fatal(1,"AXI error: unaligned read address"); end
    if (axi.awvalid && axi.awready && axi.awaddr[3:0] != 0) begin $fatal(1,"AXI error: unaligned write address"); end
  end
end

endmodule

