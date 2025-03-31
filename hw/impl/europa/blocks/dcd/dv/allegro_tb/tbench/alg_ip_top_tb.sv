




`timescale 1ps/1ps
import SramPkg::Sram;
import CtrlPkg::Ctrl;
import AxiPkg::Axi;
import JtagPkg::Jtag;

`include "decoder_if.sv"
`include "svt_axi_master_bind_if.svi"
import allegro_tb_uvm_pkg::*;

module alg_ip_top_tb;

  parameter AXI_MONITOR      = 0    ,
            USE_HW_VIP       = 0    ,
            APB_HALF_PERIOD  = 1000 ,
            AXI_HALF_PERIOD  = 1000 ,
            IP_HALF_PERIOD   = 1000 ,
            L2C_HALF_PERIOD  = 1000 ,
            MCU_HALF_PERIOD  = 1000 ;

  integer            hard_resetn_delay ;
  bit                hard_resetn       ;
  bit                aclk              ;
  bit                arstn             ;
  bit                ipclk             ;
  bit                iprstn            ;
  bit                l2cclk            ;
  bit                l2crstn           ;
  bit                mcuclk            ;
  bit                mcurstn           ;
  bit                jclk              ;
  bit                jrstn             ;
  bit                pclk              ;
  bit                prstn             ;
  bit                pclk_out          ;
  bit                prstn_out         ;
  bit                i_aclk            ;
  bit                i_ipclk           ;
  bit                i_l2cclk          ;
  bit                i_mcuclk          ;
  bit                i_jclk            ;
  bit                i_pclk            ;

  localparam C_APB_TIMEOUT = 1000;
  localparam C_AXI_TIMEOUT = (USE_HW_VIP > 0) ? 500000 : 100000;
  integer            apb_timeout_cnt;
  integer            axi_timeout_cnt;
  logic [6:0]        axi_busy;

  assign hard_resetn_delay = 4*AXI_HALF_PERIOD;

  initial
    begin
      fork
        sram.run();
        ctrl.run();
        jtag.run();
        init();
      join
    end


  task init();
    // Axelera: zero delay required due to different event order in VSIM vs VCS
    //          (otherwise hard_resetn_delay = 'x and no delay is produced)
    #0;
    #hard_resetn_delay hard_resetn = 1 ;
  endtask



  always #APB_HALF_PERIOD i_pclk      = ~i_pclk;
  always #AXI_HALF_PERIOD i_aclk      = ~i_aclk;
  always #IP_HALF_PERIOD i_ipclk      = ~i_ipclk;
  always #L2C_HALF_PERIOD i_l2cclk    = ~i_l2cclk;
  always #MCU_HALF_PERIOD i_mcuclk    = ~i_mcuclk;
  always #(MCU_HALF_PERIOD*10) i_jclk = ~i_jclk;

  
  assign pclk   = i_pclk;
  assign aclk   = i_aclk;
  assign ipclk  = i_ipclk;
  assign l2cclk = i_l2cclk;
  assign mcuclk = i_mcuclk;
  assign jclk   = i_jclk;



  always  @(posedge pclk or negedge hard_resetn)
    if ( ~hard_resetn )
      prstn <= 0;
    else
      prstn <= 1;

  always  @(posedge aclk or negedge hard_resetn)
    if ( ~hard_resetn )
      arstn <= 0;
    else
      arstn <= 1;

  always  @(posedge ipclk or negedge hard_resetn)
    if ( ~hard_resetn )
      iprstn <= 0;
    else
      iprstn <= 1;

  always  @(posedge l2cclk or negedge hard_resetn)
    if ( ~hard_resetn )
      l2crstn <= 0;
    else
      l2crstn <= 1;

  always  @(posedge mcuclk or negedge hard_resetn)
    if ( ~hard_resetn )
      mcurstn <= 0;
    else
      mcurstn <= 1;

  always  @(posedge jclk or negedge hard_resetn)
    if ( ~hard_resetn )
      jrstn <= 0;
    else
      jrstn <= 1;


Sram_if sram_if[7] (aclk);
generate
  for (genvar i = 0; i < 7; i++) begin : sram_if_load_dump
    assign sram_if[i].load = ctrl_if.load;
    assign sram_if[i].dump = ctrl_if.dump;
  end
endgenerate

Sram sram = new(sram_if);


Jtag_if jtag_if (jclk,jrstn);

Jtag jtag = new(jtag_if);

Ctrl_if ctrl_if (pclk_out,prstn_out);

Ctrl ctrl = new(ctrl_if);

assign sram_if[0].currentframe=ctrl_if.currentframe;
assign sram_if[0].maxframe=ctrl_if.maxframe;
`ifdef USE_NCSIM 
always_comb
  sram_if[0].process=ctrl_if.process;
`else
assign sram_if[0].process=ctrl_if.process;
`endif


Axi_if #(.BUS_WIDTH(128)) axi_mcu (.clk(mcuclk), .rstn(mcurstn));
Axi_if #(.BUS_WIDTH(128)) axi_if[7] (.clk(aclk), .rstn(arstn));
defparam axi_if[2].BUS_WIDTH = 128;
defparam axi_if[5].BUS_WIDTH = 32;
defparam axi_if[6].BUS_WIDTH = 32;
generate
  for (genvar i = 0; i < 7; i++) begin : axi_if_load_dump
    assign axi_if[i].bus_id = i;
    assign axi_if[i].currentframe=ctrl_if.maxframe;
  end
endgenerate


assign ctrl_if.frequency = 1000000/(2*AXI_HALF_PERIOD);

generate
  for (genvar i = 0; i < 7; i++) begin : axi_if_monitor
    if (AXI_MONITOR == 2) begin
      assign axi_if[i].time_stamp = 1;
    end else begin
      assign axi_if[i].time_stamp = 0;
    end
    if (AXI_MONITOR >= 1) begin
      initial
      begin
        fork
          axi_if[i].trace();
        join_any
      end
    end
  end
endgenerate



  always #20000000 $display("[_TOP] INFO: Simulation time: %d us", $time/1000000);




always (*xprop_off*) @(posedge pclk_out or negedge prstn) begin
  if (!prstn) begin
    apb_timeout_cnt <= '0;
  end else begin
    if (apb_timeout_cnt > C_APB_TIMEOUT) begin
      $fatal(1, "Error: TIMEOUT ON APB (apb request is too long)\n");
    end
    if (ctrl_if.enable && ctrl_if.sel) begin
      if (ctrl_if.ready) begin
        apb_timeout_cnt <= '0;
      end else begin
        apb_timeout_cnt <= apb_timeout_cnt + 1;
      end
    end
  end
end


for (genvar i=0; i < 7; i=i+1) begin : AXI_busy
  always @(*) begin
    axi_busy[i] = 1'b0;
    if ((axi_if[i].arvalid && axi_if[i].arready) ||
        (axi_if[i].awvalid && axi_if[i].awready) ||
        (axi_if[i].wvalid && axi_if[i].wready)   ||
        (axi_if[i].rvalid && axi_if[i].rready)   ||
        (axi_if[i].bvalid && axi_if[i].bready)) begin
        axi_busy[i]  <= 1'b1;
    end
  end
end



always (*xprop_off*) @(posedge aclk or negedge arstn) begin
  if (!arstn) begin
    axi_timeout_cnt <= '0;
  end else begin
    if (axi_timeout_cnt > C_AXI_TIMEOUT) begin
      $fatal(1, "Error: TIMEOUT ON AXI (axi is idle too long)\n");
    end
    if (axi_busy || ctrl_if.ready) begin
      axi_timeout_cnt <= 0;
    end else begin
      axi_timeout_cnt <= axi_timeout_cnt + 1;
    end
  end
end


for (genvar i=0; i < 7; i=i+1) begin : AXI
  if(i==2) begin
   
    alg_amba_axi2sram #(.CHECK_ALIGN(0)) I_AXI2SRAM (
      .axi    (axi_if[i]),
      .sram   (sram_if[i])
    );
  end else begin
    alg_amba_axi2sram I_AXI2SRAM (
      .axi    (axi_if[i]),
      .sram   (sram_if[i])
    );
  end
end

`include "decoder_scoreboard_binding.sv"

// Axelera: For system-level testcases, offset APB addresses to match top-level address map.
bit [31:0] apb_addr_offset = 32'h0;
initial begin
  if ($test$plusargs("CODEC_SYSTEM_LEVEL_TESTCASE"))
    apb_addr_offset = 32'hB0000000 - 32'h00080000;
end

  alg_ip_top #(
    .REMOVE_ID               (0),
    .USE_HW_VIP              (USE_HW_VIP)
   ) dut (
    .sys_clk                 (ipclk),
    .sys_rstn                (iprstn),
    .mcu_clk                 (mcuclk),
    .mcu_rstn                (mcurstn),
    .debug_clk               (jtag_if.tck),
    .debug_sys_rst           (1'b0),
    .debug_rst               (jtag_if.trst),
    .debug_capture           (1'b0),
    .debug_reg_en            (8'h00),
    .debug_shift             (1'b0),
    .debug_tdi               (jtag_if.tdi),
    .debug_tdo               (jtag_if.tdo),
    .debug_update            (jtag_if.tms),
    .l2c_clk                 (l2cclk),
    .l2c_rstn                (l2crstn),
    .l2c_tx                  (),
    .l2c_rx                  (357'h0),
    .prstn                   (prstn),
    .prstn_out               (prstn_out),
    .pclk                    (pclk),
    .pclk_out                (pclk_out),
    .psel                    (ctrl_if.sel),
    .pslverr                 (),
    .penable                 (ctrl_if.enable),
    .pwrite                  (ctrl_if.write),
    .pwdata                  (ctrl_if.wdata),
    .paddr                   (ctrl_if.addr - apb_addr_offset),
    .prdata                  (ctrl_if.rdata),
    .pready                  (ctrl_if.ready),
    .pintreq                 (ctrl_if.pintreq),
    .aclk                    (aclk),
    .aclk_nobuf              (aclk),
    .arstn                   (arstn),
    .araddr0                 (axi_if[0].araddr),
    .arburst0                (axi_if[0].arburst),
    .arid0                   (axi_if[0].arid),
    .arlen0                  (axi_if[0].arlen),
    .arready0                (axi_if[0].arready),
    .arsize0                 (axi_if[0].arsize),
    .arvalid0                (axi_if[0].arvalid),
    .awaddr0                 (axi_if[0].awaddr),
    .awburst0                (axi_if[0].awburst),
    .awid0                   (axi_if[0].awid),
    .awlen0                  (axi_if[0].awlen),
    .awready0                (axi_if[0].awready),
    .awsize0                 (axi_if[0].awsize),
    .awvalid0                (axi_if[0].awvalid),
    .bready0                 (axi_if[0].bready),
    .bvalid0                 (axi_if[0].bvalid),
    .bresp0                  (axi_if[0].bresp[0]),
    .bid0                    (axi_if[0].bid),
    .rdata0                  (axi_if[0].rdata),
    .rid0                    (axi_if[0].rid),
    .rlast0                  (axi_if[0].rlast),
    .rready0                 (axi_if[0].rready),
    .rvalid0                 (axi_if[0].rvalid),
    .rresp0                  (axi_if[0].rresp[0]),
    .wdata0                  (axi_if[0].wdata),
    .wstrb0                  (axi_if[0].wstrb),
    .wlast0                  (axi_if[0].wlast),
    .wready0                 (axi_if[0].wready),
    .wvalid0                 (axi_if[0].wvalid),
    .araddr1                 (axi_if[1].araddr),
    .arburst1                (axi_if[1].arburst),
    .arid1                   (axi_if[1].arid),
    .arlen1                  (axi_if[1].arlen),
    .arready1                (axi_if[1].arready),
    .arsize1                 (axi_if[1].arsize),
    .arvalid1                (axi_if[1].arvalid),
    .awaddr1                 (axi_if[1].awaddr),
    .awburst1                (axi_if[1].awburst),
    .awid1                   (axi_if[1].awid),
    .awlen1                  (axi_if[1].awlen),
    .awready1                (axi_if[1].awready),
    .awsize1                 (axi_if[1].awsize),
    .awvalid1                (axi_if[1].awvalid),
    .bready1                 (axi_if[1].bready),
    .bvalid1                 (axi_if[1].bvalid),
    .bresp1                  (axi_if[1].bresp[0]),
    .bid1                    (axi_if[1].bid),
    .rdata1                  (axi_if[1].rdata),
    .rid1                    (axi_if[1].rid),
    .rlast1                  (axi_if[1].rlast),
    .rready1                 (axi_if[1].rready),
    .rvalid1                 (axi_if[1].rvalid),
    .rresp1                  (axi_if[1].rresp[0]),
    .wdata1                  (axi_if[1].wdata),
    .wstrb1                  (axi_if[1].wstrb),
    .wlast1                  (axi_if[1].wlast),
    .wready1                 (axi_if[1].wready),
    .wvalid1                 (axi_if[1].wvalid),
    .araddr3                 (axi_if[3].araddr),
    .arburst3                (axi_if[3].arburst),
    .arid3                   (axi_if[3].arid),
    .arlen3                  (axi_if[3].arlen),
    .arready3                (axi_if[3].arready),
    .arsize3                 (axi_if[3].arsize),
    .arvalid3                (axi_if[3].arvalid),
    .awaddr3                 (axi_if[3].awaddr),
    .awburst3                (axi_if[3].awburst),
    .awid3                   (axi_if[3].awid),
    .awlen3                  (axi_if[3].awlen),
    .awready3                (axi_if[3].awready),
    .awsize3                 (axi_if[3].awsize),
    .awvalid3                (axi_if[3].awvalid),
    .bready3                 (axi_if[3].bready),
    .bvalid3                 (axi_if[3].bvalid),
    .bresp3                  (axi_if[3].bresp[0]),
    .bid3                    (axi_if[3].bid),
    .rdata3                  (axi_if[3].rdata),
    .rid3                    (axi_if[3].rid),
    .rlast3                  (axi_if[3].rlast),
    .rready3                 (axi_if[3].rready),
    .rvalid3                 (axi_if[3].rvalid),
    .rresp3                  (axi_if[3].rresp[0]),
    .wdata3                  (axi_if[3].wdata),
    .wstrb3                  (axi_if[3].wstrb),
    .wlast3                  (axi_if[3].wlast),
    .wready3                 (axi_if[3].wready),
    .wvalid3                 (axi_if[3].wvalid),
    .araddr4                 (axi_if[4].araddr),
    .arburst4                (axi_if[4].arburst),
    .arid4                   (axi_if[4].arid),
    .arlen4                  (axi_if[4].arlen),
    .arready4                (axi_if[4].arready),
    .arsize4                 (axi_if[4].arsize),
    .arvalid4                (axi_if[4].arvalid),
    .awaddr4                 (axi_if[4].awaddr),
    .awburst4                (axi_if[4].awburst),
    .awid4                   (axi_if[4].awid),
    .awlen4                  (axi_if[4].awlen),
    .awready4                (axi_if[4].awready),
    .awsize4                 (axi_if[4].awsize),
    .awvalid4                (axi_if[4].awvalid),
    .bready4                 (axi_if[4].bready),
    .bvalid4                 (axi_if[4].bvalid),
    .bresp4                  (axi_if[4].bresp[0]),
    .bid4                    (axi_if[4].bid),
    .rdata4                  (axi_if[4].rdata),
    .rid4                    (axi_if[4].rid),
    .rlast4                  (axi_if[4].rlast),
    .rready4                 (axi_if[4].rready),
    .rvalid4                 (axi_if[4].rvalid),
    .rresp4                  (axi_if[4].rresp[0]),
    .wdata4                  (axi_if[4].wdata),
    .wstrb4                  (axi_if[4].wstrb),
    .wlast4                  (axi_if[4].wlast),
    .wready4                 (axi_if[4].wready),
    .wvalid4                 (axi_if[4].wvalid),
    .araddr2                 (axi_mcu.araddr),
    .arburst2                (axi_mcu.arburst),
    .arid2                   (axi_mcu.arid),
    .arlen2                  (axi_mcu.arlen),
    .arready2                (axi_mcu.arready),
    .arsize2                 (axi_mcu.arsize),
    .arvalid2                (axi_mcu.arvalid),
    .awaddr2                 (axi_mcu.awaddr),
    .awburst2                (axi_mcu.awburst),
    .awid2                   (axi_mcu.awid),
    .awlen2                  (axi_mcu.awlen),
    .awready2                (axi_mcu.awready),
    .awsize2                 (axi_mcu.awsize),
    .awvalid2                (axi_mcu.awvalid),
    .bready2                 (axi_mcu.bready),
    .bvalid2                 (axi_mcu.bvalid),
    .bresp2                  (axi_mcu.bresp[0]),
    .bid2                    (axi_mcu.bid),
    .rdata2                  (axi_mcu.rdata[128-1:0]),
    .rid2                    (axi_mcu.rid),
    .rlast2                  (axi_mcu.rlast),
    .rready2                 (axi_mcu.rready),
    .rvalid2                 (axi_mcu.rvalid),
    .rresp2                  (axi_mcu.rresp[0]),
    .wdata2                  (axi_mcu.wdata[128-1:0]),
    .wstrb2                  (axi_mcu.wstrb[(128/8)-1:0]),
    .wlast2                  (axi_mcu.wlast),
    .wready2                 (axi_mcu.wready),
    .wvalid2                 (axi_mcu.wvalid),
    .m_axi_dc_araddr         (axi_if[5].araddr),
    .m_axi_dc_arburst        (axi_if[5].arburst),
    .m_axi_dc_arcache        (),
    .m_axi_dc_arid           (axi_if[5].arid[0]),
    .m_axi_dc_arlen          (axi_if[5].arlen),
    .m_axi_dc_arlock         (),
    .m_axi_dc_arprot         (),
    .m_axi_dc_arqos          (),
    .m_axi_dc_arready        (axi_if[5].arready),
    .m_axi_dc_arsize         (axi_if[5].arsize),
    .m_axi_dc_arvalid        (axi_if[5].arvalid),
    .m_axi_dc_awaddr         (axi_if[5].awaddr),
    .m_axi_dc_awburst        (axi_if[5].awburst),
    .m_axi_dc_awcache        (),
    .m_axi_dc_awid           (axi_if[5].awid[0]),
    .m_axi_dc_awlen          (axi_if[5].awlen),
    .m_axi_dc_awlock         (),
    .m_axi_dc_awprot         (),
    .m_axi_dc_awqos          (),
    .m_axi_dc_awready        (axi_if[5].awready),
    .m_axi_dc_awsize         (axi_if[5].awsize),
    .m_axi_dc_awvalid        (axi_if[5].awvalid),
    .m_axi_dc_bid            (axi_if[5].bid[0]),
    .m_axi_dc_bready         (axi_if[5].bready),
    .m_axi_dc_bresp          (axi_if[5].bresp),
    .m_axi_dc_bvalid         (axi_if[5].bvalid),
    .m_axi_dc_rdata          (axi_if[5].rdata[31:0]),
    .m_axi_dc_rid            (axi_if[5].rid[0]),
    .m_axi_dc_rlast          (axi_if[5].rlast),
    .m_axi_dc_rready         (axi_if[5].rready),
    .m_axi_dc_rresp          (axi_if[5].rresp),
    .m_axi_dc_rvalid         (axi_if[5].rvalid),
    .m_axi_dc_wdata          (axi_if[5].wdata[31:0]),
    .m_axi_dc_wlast          (axi_if[5].wlast),
    .m_axi_dc_wready         (axi_if[5].wready),
    .m_axi_dc_wstrb          (axi_if[5].wstrb[3:0]),
    .m_axi_dc_wvalid         (axi_if[5].wvalid),
    .m_axi_ic_araddr         (axi_if[6].araddr),
    .m_axi_ic_arburst        (axi_if[6].arburst),
    .m_axi_ic_arcache        (),
    .m_axi_ic_arid           (axi_if[6].arid[0]),
    .m_axi_ic_arlen          (axi_if[6].arlen),
    .m_axi_ic_arlock         (),
    .m_axi_ic_arprot         (),
    .m_axi_ic_arqos          (),
    .m_axi_ic_arready        (axi_if[6].arready),
    .m_axi_ic_arsize         (axi_if[6].arsize),
    .m_axi_ic_arvalid        (axi_if[6].arvalid),
    .m_axi_ic_awaddr         (axi_if[6].awaddr),
    .m_axi_ic_awburst        (axi_if[6].awburst),
    .m_axi_ic_awcache        (),
    .m_axi_ic_awid           (axi_if[6].awid[0]),
    .m_axi_ic_awlen          (axi_if[6].awlen),
    .m_axi_ic_awlock         (),
    .m_axi_ic_awprot         (),
    .m_axi_ic_awqos          (),
    .m_axi_ic_awready        (axi_if[6].awready),
    .m_axi_ic_awsize         (axi_if[6].awsize),
    .m_axi_ic_awvalid        (axi_if[6].awvalid),
    .m_axi_ic_bid            (axi_if[6].bid[0]),
    .m_axi_ic_bready         (axi_if[6].bready),
    .m_axi_ic_bresp          (axi_if[6].bresp),
    .m_axi_ic_bvalid         (axi_if[6].bvalid),
    .m_axi_ic_rdata          (axi_if[6].rdata[31:0]),
    .m_axi_ic_rid            (axi_if[6].rid[0]),
    .m_axi_ic_rlast          (axi_if[6].rlast),
    .m_axi_ic_rready         (axi_if[6].rready),
    .m_axi_ic_rresp          (axi_if[6].rresp),
    .m_axi_ic_rvalid         (axi_if[6].rvalid),
    .m_axi_ic_wdata          (axi_if[6].wdata[31:0]),
    .m_axi_ic_wlast          (axi_if[6].wlast),
    .m_axi_ic_wready         (axi_if[6].wready),
    .m_axi_ic_wstrb          (axi_if[6].wstrb[3:0]),
    .m_axi_ic_wvalid         (axi_if[6].wvalid)
  );


  alg_amba_axi2axi_async #(
    .AXI_DATA_WIDTH (128)
  ) AXI_MCU_ASYNC_BRIDGE (
    .r_clk       (aclk),
    .r_rstn      (arstn),
    .r_araddr    (axi_if[2].araddr),
    .r_arburst   (axi_if[2].arburst),
    .r_arid      (axi_if[2].arid),
    .r_arlen     (axi_if[2].arlen),
    .r_arready   (axi_if[2].arready),
    .r_arsize    (axi_if[2].arsize),
    .r_arvalid   (axi_if[2].arvalid),
    .r_awaddr    (axi_if[2].awaddr),
    .r_awburst   (axi_if[2].awburst),
    .r_awid      (axi_if[2].awid),
    .r_awlen     (axi_if[2].awlen),
    .r_awready   (axi_if[2].awready),
    .r_awsize    (axi_if[2].awsize),
    .r_awvalid   (axi_if[2].awvalid),
    .r_bready    (axi_if[2].bready),
    .r_bvalid    (axi_if[2].bvalid),
    .r_bresp     (axi_if[2].bresp),
    .r_bid       (axi_if[2].bid),
    .r_rdata     (axi_if[2].rdata),
    .r_rid       (axi_if[2].rid),
    .r_rlast     (axi_if[2].rlast),
    .r_rready    (axi_if[2].rready),
    .r_rvalid    (axi_if[2].rvalid),
    .r_rresp     (axi_if[2].rresp),
    .r_wdata     (axi_if[2].wdata),
    .r_wstrb     (axi_if[2].wstrb),
    .r_wlast     (axi_if[2].wlast),
    .r_wready    (axi_if[2].wready),
    .r_wvalid    (axi_if[2].wvalid),
    .w_clk       (mcuclk),
    .w_rstn      (mcurstn),
    .w_araddr    (axi_mcu.araddr),
    .w_arburst   (axi_mcu.arburst),
    .w_arid      (axi_mcu.arid),
    .w_arlen     (axi_mcu.arlen),
    .w_arready   (axi_mcu.arready),
    .w_arsize    (axi_mcu.arsize),
    .w_arvalid   (axi_mcu.arvalid),
    .w_awaddr    (axi_mcu.awaddr),
    .w_awburst   (axi_mcu.awburst),
    .w_awid      (axi_mcu.awid),
    .w_awlen     (axi_mcu.awlen),
    .w_awready   (axi_mcu.awready),
    .w_awsize    (axi_mcu.awsize),
    .w_awvalid   (axi_mcu.awvalid),
    .w_bready    (axi_mcu.bready),
    .w_bvalid    (axi_mcu.bvalid),
    .w_bresp     (axi_mcu.bresp),
    .w_bid       (axi_mcu.bid),
    .w_rdata     (axi_mcu.rdata),
    .w_rid       (axi_mcu.rid),
    .w_rlast     (axi_mcu.rlast),
    .w_rready    (axi_mcu.rready),
    .w_rvalid    (axi_mcu.rvalid),
    .w_rresp     (axi_mcu.rresp),
    .w_wdata     (axi_mcu.wdata),
    .w_wstrb     (axi_mcu.wstrb),
    .w_wlast     (axi_mcu.wlast),
    .w_wready    (axi_mcu.wready),
    .w_wvalid    (axi_mcu.wvalid)
  );


for(genvar i=0; i < 7; i++) begin
  assign axi_if[i].rresp      = {1'b0, ctrl_if.drive[(i/2)+4]};
  assign axi_if[i].bresp      = {1'b0, ctrl_if.drive[(i/2)+5]};
end
assign axi_if[5].awid[4:1]  = 4'h0;
assign axi_if[6].awid[4:1]  = 4'h0;
assign axi_if[5].arid[4:1]  = 4'h0;
assign axi_if[6].arid[4:1]  = 4'h0;




  alg_ip_waves
    waves
    (
      .clk      (pclk_out       ),
      .frm_done (ctrl_if.dump   ),
      .process  (ctrl_if.process)
    );



endmodule 

