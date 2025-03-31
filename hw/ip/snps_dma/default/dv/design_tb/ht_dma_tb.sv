// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: SNSP DMA testbench, simple directed "test" moving data
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`include "axi_intf.sv"

module ht_dma_tb;
  import tb_axi_pkg::*;
  localparam AW = 40;
  localparam AXI_DW = 64;
  localparam IDW = 6;
  localparam BW = 8;

  localparam DW = 512;
  localparam PWORD_LEN = 64;
  localparam EL_DW = DW / PWORD_LEN;

  localparam TOK_PROD = 5;
  localparam TOK_CONS = 3;

  localparam PAYLOAD_W = 'h40; // no cmdblock yet, so not yet known...

  parameter longint LEG_CSR_ST_ADDR   = 'h2620000;
  parameter longint LEG_CSR_END_ADDR  = 'h262FFFF;
  parameter longint CH1_CSR_ST_ADDR   = 'h2600000;
  parameter longint CH1_CSR_END_ADDR  = 'h260FFFF;
  parameter longint CH1_CMD_ST_ADDR   = 'h2E00000;
  parameter longint CH1_CMD_END_ADDR  = 'h2E1FFFF;
  parameter longint CH2_CSR_ST_ADDR   = 'h2610000;
  parameter longint CH2_CSR_END_ADDR  = 'h261FFFF;
  parameter longint CH2_CMD_ST_ADDR   = 'h2E20000;
  parameter longint CH2_CMD_END_ADDR  = 'h2E21FFF;

  logic tb_clk;
  logic tb_rst_n;

  //////// AXI drivers
  axi_intf #(.DW(AXI_DW), .AW(AW), .IDW(IDW))  cfg_axi_if ();
  axi_cmdblock_driver  #(
    .DW(AXI_DW),
    .AW(AW),
    .IDW(IDW)
  ) cfg_cmdb_drv = new (
    "DMA_CFG_CMDB_DRV", cfg_axi_if
  );

  axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) m1_axi_if ();
  axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) m2_axi_if ();
  axi_sl_driver #(
    .DW(DW), .AW(AW), .IDW(IDW)
  ) dma_m1_drv = new(
    "DMA_M1_AXI", m1_axi_if
  );
  axi_sl_driver #(
    .DW(DW), .AW(AW), .IDW(IDW)
  ) dma_m2_drv = new(
    "DMA_M2_AXI", m2_axi_if
  );

  int dev_leg = 0;
  int dev_ch1 = 1;
  int dev_ch2 = 2;

  initial begin
    cfg_cmdb_drv.set_csr_base(LEG_CSR_ST_ADDR, .dev(dev_leg));
    cfg_cmdb_drv.set_id(.id(1), .dev(dev_leg));
    cfg_cmdb_drv.set_csr_base(CH1_CSR_ST_ADDR, .dev(dev_ch1));
    cfg_cmdb_drv.set_cmd_base(CH1_CMD_ST_ADDR, .dev(dev_ch1));
    cfg_cmdb_drv.set_id(.id(2), .dev(dev_ch1));
    cfg_cmdb_drv.set_csr_base(CH2_CSR_ST_ADDR, .dev(dev_ch2));
    cfg_cmdb_drv.set_cmd_base(CH2_CMD_ST_ADDR, .dev(dev_ch2));
    cfg_cmdb_drv.set_id(.id(3), .dev(dev_ch2));
  end

  assign cfg_axi_if.clk = tb_clk;
  assign cfg_axi_if.rst_n = tb_rst_n;
  assign m1_axi_if.clk = tb_clk;
  assign m1_axi_if.rst_n = tb_rst_n;
  assign m2_axi_if.clk = tb_clk;
  assign m2_axi_if.rst_n = tb_rst_n;

  // clock generation:
  initial begin
    tb_clk = 0;
    forever #((0.800) / 2) tb_clk = ~tb_clk;
  end

  // reset generation:
  initial begin
    tb_rst_n = 0;
    repeat (20) @(posedge tb_clk);
    #1;
    tb_rst_n = 1;
  end

  initial begin
    $display("Start drivers... @ %0t", $time());
    fork
      cfg_cmdb_drv.run();
      dma_m1_drv.run();
      dma_m2_drv.run();
    join
    $display("Start drivers: done @ %0t", $time());
  end

  ////////////////////////////////////////////////////////
  // DUT:
  snps_dma #(
    .DMA_VERSION("aic_ht"),

    .NR_REGIONS(5),

    .REGION_SLAVE_ID('{snps_dma_pkg::legacy_idx,
                      snps_dma_pkg::csr_base_idx+0,
                      snps_dma_pkg::cmd_base_idx+0,
                      snps_dma_pkg::csr_base_idx+2,
                      snps_dma_pkg::cmd_base_idx+2}),
    .REGION_ST_ADDR('{LEG_CSR_ST_ADDR,
                      CH1_CSR_ST_ADDR,
                      CH1_CMD_ST_ADDR,
                      CH2_CSR_ST_ADDR,
                      CH2_CMD_ST_ADDR}),
    .REGION_END_ADDR('{LEG_CSR_END_ADDR,
                      CH1_CSR_END_ADDR,
                      CH1_CMD_END_ADDR,
                      CH2_CSR_END_ADDR,
                      CH2_CMD_END_ADDR}),

    .SL_AW(40),
    .SL_DW(64),
    .SL_IDW(6),
    .SL_BW(8),

    .NR_TOK_PROD(3),
    .NR_TOK_CONS(3)
  ) u_dut (
    .i_clk(tb_clk),
    .i_rst_n(tb_rst_n),
    .i_test_mode('0),

    ///// AXI subordinate:
    // Write Address Channel
    .i_awid(cfg_axi_if.awid),
    .i_awaddr(cfg_axi_if.awaddr),
    .i_awlen(cfg_axi_if.awlen),
    .i_awsize(cfg_axi_if.awsize),
    .i_awburst(cfg_axi_if.awburst),
    .i_awvalid(cfg_axi_if.awvalid),
    .o_awready(cfg_axi_if.awready),
    // Read Address Channel
    .i_arid(cfg_axi_if.arid),
    .i_araddr(cfg_axi_if.araddr),
    .i_arlen(cfg_axi_if.arlen),
    .i_arsize(cfg_axi_if.arsize),
    .i_arburst(cfg_axi_if.arburst),
    .i_arvalid(cfg_axi_if.arvalid),
    .o_arready(cfg_axi_if.arready),
    // Write  Data Channel
    .i_wdata(cfg_axi_if.wdata),
    .i_wstrb(cfg_axi_if.wstrb),
    .i_wlast(cfg_axi_if.wlast),
    .i_wvalid(cfg_axi_if.wvalid),
    .o_wready(cfg_axi_if.wready),
    // Read Data Channel
    .o_rid(cfg_axi_if.rid),
    .o_rdata(cfg_axi_if.rdata),
    .o_rresp(cfg_axi_if.rresp),
    .o_rlast(cfg_axi_if.rlast),
    .o_rvalid(cfg_axi_if.rvalid),
    .i_rready(cfg_axi_if.rready),
    // Write Response Channel
    .o_bid(cfg_axi_if.bid),
    .o_bresp(cfg_axi_if.bresp),
    .o_bvalid(cfg_axi_if.bvalid),
    .i_bready(cfg_axi_if.bready),

    ///// AXI managers:
    // Write Address Channel
    .o_axi_m_awid({m2_axi_if.awid, m1_axi_if.awid}),
    .o_axi_m_awaddr({m2_axi_if.awaddr, m1_axi_if.awaddr}),
    .o_axi_m_awlen({m2_axi_if.awlen, m1_axi_if.awlen}),
    .o_axi_m_awsize({m2_axi_if.awsize, m1_axi_if.awsize}),
    .o_axi_m_awburst({m2_axi_if.awburst, m1_axi_if.awburst}),
    .o_axi_m_awlock({m2_axi_if.awlock, m1_axi_if.awlock}),
    .o_axi_m_awcache({m2_axi_if.awcache, m1_axi_if.awcache}),
    .o_axi_m_awprot({m2_axi_if.awprot, m1_axi_if.awprot}),
    .o_axi_m_awvalid({m2_axi_if.awvalid, m1_axi_if.awvalid}),
    .i_axi_m_awready({m2_axi_if.awready, m1_axi_if.awready}),
    // Read Address Channel
    .o_axi_m_arid({m2_axi_if.arid, m1_axi_if.arid}),
    .o_axi_m_araddr({m2_axi_if.araddr, m1_axi_if.araddr}),
    .o_axi_m_arlen({m2_axi_if.arlen, m1_axi_if.arlen}),
    .o_axi_m_arsize({m2_axi_if.arsize, m1_axi_if.arsize}),
    .o_axi_m_arburst({m2_axi_if.arburst, m1_axi_if.arburst}),
    .o_axi_m_arlock({m2_axi_if.arlock, m1_axi_if.arlock}),
    .o_axi_m_arcache({m2_axi_if.arcache, m1_axi_if.arcache}),
    .o_axi_m_arprot({m2_axi_if.arprot, m1_axi_if.arprot}),
    .o_axi_m_arvalid({m2_axi_if.arvalid, m1_axi_if.arvalid}),
    .i_axi_m_arready({m2_axi_if.arready, m1_axi_if.arready}),
    // Write  Data Channel
    .o_axi_m_wdata({m2_axi_if.wdata, m1_axi_if.wdata}),
    .o_axi_m_wstrb({m2_axi_if.wstrb, m1_axi_if.wstrb}),
    .o_axi_m_wlast({m2_axi_if.wlast, m1_axi_if.wlast}),
    .o_axi_m_wvalid({m2_axi_if.wvalid, m1_axi_if.wvalid}),
    .i_axi_m_wready({m2_axi_if.wready, m1_axi_if.wready}),
    // Read Data Channel
    .i_axi_m_rid({m2_axi_if.rid, m1_axi_if.rid}),
    .i_axi_m_rdata({m2_axi_if.rdata, m1_axi_if.rdata}),
    .i_axi_m_rresp({m2_axi_if.rresp, m1_axi_if.rresp}),
    .i_axi_m_rlast({m2_axi_if.rlast, m1_axi_if.rlast}),
    .i_axi_m_rvalid({m2_axi_if.rvalid, m1_axi_if.rvalid}),
    .o_axi_m_rready({m2_axi_if.rready, m1_axi_if.rready}),
    // Write Response Channel
    .i_axi_m_bid({m2_axi_if.bid, m1_axi_if.bid}),
    .i_axi_m_bresp({m2_axi_if.bresp, m1_axi_if.bresp}),
    .i_axi_m_bvalid({m2_axi_if.bvalid, m1_axi_if.bvalid}),
    .o_axi_m_bready({m2_axi_if.bready, m1_axi_if.bready}),

    // Interrupts
    .o_irq_ch(),
    .o_irq_cmn(),

    .o_tok_prod_vld(),
    .i_tok_prod_rdy('1),
    .i_tok_cons_vld('0),
    .o_tok_cons_rdy(),

    ///// Timestamp:
    .o_ts_start(),
    .o_ts_end(),
    ///// ACD sync:
    .o_acd_sync(),

     // SRAM config registers
    .i_impl_inp(),
    .o_impl_oup(),

    // Debug signals
    .i_debug_ch_num('0),
    .o_dma_debug()

);
  ////////////////////////////////////////////////////////
  

  initial begin
    logic [AXI_DW-1:0] rd_data;
    logic [AW-1:0] sar;
    logic [AW-1:0] dar;
    logic [AXI_DW-1:0] ts;
    int errors = 0;
    
    wait(tb_rst_n);
    repeat (5) @(posedge tb_clk);

    sar = 'h1000;
    dar = 'h2000;
    ts  = 'h2;

    cfg_cmdb_drv.csr_wr(snps_dma_cmdb_csr_reg_pkg::SNPS_DMA_CMDB_CSR_DBG_SCRATCH_OFFSET/8, 'hb1a, .dev(dev_ch1));
    cfg_cmdb_drv.csr_wr(snps_dma_cmdb_csr_reg_pkg::SNPS_DMA_CMDB_CSR_DBG_SCRATCH_OFFSET/8, 'hb1a, .dev(dev_ch2));

    $display("DMA HT Legacy test: configure DMA for a transfer from 0x%h to 0x%h with TS %0d... @ %0t", sar, dar, ts, $time());
    cfg_cmdb_drv.csr_wr(2, 1, .dev(dev_leg));            // enable DMA
    cfg_cmdb_drv.csr_wr('h100/8, sar, .dev(dev_leg)); // SAR
    cfg_cmdb_drv.csr_wr('h108/8, dar, .dev(dev_leg)); // DAR
    cfg_cmdb_drv.csr_wr('h110/8, ts, .dev(dev_leg));   // TS

    cfg_cmdb_drv.csr_wr('h118/8, (0              |  // CH1_CTL [63:0]:
                                    ('b0 << 63)     |  // [63] shadow reg or lli used
                                    ('b1 << 62)     |  // [62] shadow reg or lli last, last block to transfer
                                    ('b0 << 58)     |  // [58] Int on completion of block,
                                    ('h1f << 48)    |  // [55:48] awlen
                                    ('b1 << 47)     |  // [47] awlen_en
                                    ('h1f << 39)    |  // [46:39] arlen
                                    ('b1 << 38)     |  // [38] arlen_en
                                    ('b1 << 30)     |  // [30] last write must be non-posted
                                    ('h8 << 18)     |  // [21:18] dst_msize, 512 items
                                    ('h8 << 14)     |  // [17:14] src_msize, 512 items
                                    ('h6 << 11)     |  // [13:11] dst_tr_width, 512 bits
                                    ('h6 << 8)      |  // [10:8] src_tr_width, 512 bits
                                    (1 << 2)        |  // [2] DMS, dest master select (mt2)
                                    (0 << 0)), .dev(dev_leg));        // [0] SMS, src master select (mt1)
    cfg_cmdb_drv.csr_wr('h120/8, (0              | // CH1_CFG [63:0]
                                    ('h4 << 59)     |  // [62:59] dst osr lmt
                                    ('h4 << 55)     |  // [58:55] src osr lmt
                                    ('h0 << 32)     |  // [34:32] mem2mem dmac, no handshake
                                    ('h0 << 2)      |  // [3:2] DST_MULTBLK_TYPE (LL)
                                    ('h0 << 0)), .dev(dev_leg));      // [1:0] SRC_MULTBLK_TYPE (LL)


    $display("DMA HT Legacy test: enable channel 1 to start transfer... @ %0t", $time());
    cfg_cmdb_drv.csr_wr('h18/8, 'h101, .dev(dev_leg));    // enable channel 1
    
    #20;

    $display("DMA HT Legacy test: Waiting for DMA to become idle... @ %0t", $time());
    // wait until all channels are idle
    do begin
        repeat(1) @(posedge tb_clk);
        cfg_cmdb_drv.csr_rd('h18/8, rd_data, .dev(dev_leg));
        // $info("Read as enable status: %h", rd_data);
        repeat(10) @(posedge tb_clk);
    end while (rd_data != 0);

    $display("DMA HT Legacy test: Compare data in source and destination... @ %0t", $time());
    // bit of data checking:
    for (int i=0; i<ts; i++) begin
      if (dma_m1_drv.get_rdata(sar+(i*(DW/8))) != dma_m2_drv.get_rdata(dar+(i*(DW/8)))) begin
        errors = errors + 1;
        $error("ERROR found! Data at SAR 0x%h and DAR 0x%h don't match!", sar+(i*(DW/8)), dar+(i*(DW/8)));
        $display("SRC: 0x%h", dma_m1_drv.get_rdata(sar+(i*(DW/8))));
        $display("DST: 0x%h", dma_m2_drv.get_rdata(dar+(i*(DW/8))));
      end
    end

    $display("All done with %0d errors! @ %0t", errors, $time());

    $finish;
  end

  ////////////////////////////////////////////////////////
endmodule
