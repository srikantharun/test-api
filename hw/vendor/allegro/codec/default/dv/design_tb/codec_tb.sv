// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Leonidas Katselas <leonidas.katselas@axelera.ai>


/// TODO:__one_line_summary_of_codec_tb__
///
module codec_tb;
  import allegro_codec_pkg::*;
  // Set to 1.2 GHz
  localparam realtime TbCycleTime = 0.8333ns;

  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  // Clock / Reset genereration and stop of simulation
  logic tb_clk;
  logic tb_pclk;
  logic tb_rst_n;  

  /// AXI master 0 write address signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] o_dec_0_axi_m_awid;
  logic [      CODEC_AXI_ADDR_WIDTH-1:0] o_dec_0_axi_m_awaddr;
  logic [       CODEC_AXI_LEN_WIDTH-1:0] o_dec_0_axi_m_awlen;
  logic [      CODEC_AXI_SIZE_WIDTH-1:0] o_dec_0_axi_m_awsize;
  logic [      CODEC_AXI_PROT_WIDTH-1:0] o_dec_0_axi_m_awprot;
  logic [CODEC_AXI_BURST_TYPE_WIDTH-1:0] o_dec_0_axi_m_awburst;
  logic                                  o_dec_0_axi_m_awvalid;
  logic                                  i_dec_0_axi_m_awready;
  /// AXI master 0 write data signals
  logic [      CODEC_AXI_DATA_WIDTH-1:0] o_dec_0_axi_m_wdata;
  logic [     CODEC_AXI_WSTRB_WIDTH-1:0] o_dec_0_axi_m_wstrb;
  logic                                  o_dec_0_axi_m_wlast;
  logic                                  o_dec_0_axi_m_wvalid;
  logic                                  i_dec_0_axi_m_wready;
  /// AXI master 0 write response signals
  logic [      CODEC_AXI_RESP_WIDTH-1:0] i_dec_0_axi_m_bresp;
  logic [        CODEC_AXI_ID_WIDTH-1:0] i_dec_0_axi_m_bid;
  logic                                  i_dec_0_axi_m_bvalid;
  logic                                  o_dec_0_axi_m_bready;
  /// AXI master 0 read address signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] o_dec_0_axi_m_arid;
  logic [      CODEC_AXI_ADDR_WIDTH-1:0] o_dec_0_axi_m_araddr;
  logic [       CODEC_AXI_LEN_WIDTH-1:0] o_dec_0_axi_m_arlen;
  logic [      CODEC_AXI_SIZE_WIDTH-1:0] o_dec_0_axi_m_arsize;
  logic [      CODEC_AXI_PROT_WIDTH-1:0] o_dec_0_axi_m_arprot;
  logic [CODEC_AXI_BURST_TYPE_WIDTH-1:0] o_dec_0_axi_m_arburst;
  logic                                  o_dec_0_axi_m_arvalid;
  logic                                  i_dec_0_axi_m_arready;
  /// AXI master 0 read data signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] i_dec_0_axi_m_rid;
  logic [      CODEC_AXI_DATA_WIDTH-1:0] i_dec_0_axi_m_rdata;
  logic                                  i_dec_0_axi_m_rlast;
  logic [      CODEC_AXI_RESP_WIDTH-1:0] i_dec_0_axi_m_rresp;
  logic                                  i_dec_0_axi_m_rvalid;
  logic                                  o_dec_0_axi_m_rready;
  /// AXI master 1 write address signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] o_dec_1_axi_m_awid;
  logic [      CODEC_AXI_ADDR_WIDTH-1:0] o_dec_1_axi_m_awaddr;
  logic [       CODEC_AXI_LEN_WIDTH-1:0] o_dec_1_axi_m_awlen;
  logic [      CODEC_AXI_SIZE_WIDTH-1:0] o_dec_1_axi_m_awsize;
  logic [      CODEC_AXI_PROT_WIDTH-1:0] o_dec_1_axi_m_awprot;
  logic [CODEC_AXI_BURST_TYPE_WIDTH-1:0] o_dec_1_axi_m_awburst;
  logic                                  o_dec_1_axi_m_awvalid;
  logic                                  i_dec_1_axi_m_awready;
  /// AXI master 1 write data signals
  logic [      CODEC_AXI_DATA_WIDTH-1:0] o_dec_1_axi_m_wdata;
  logic [     CODEC_AXI_WSTRB_WIDTH-1:0] o_dec_1_axi_m_wstrb;
  logic                                  o_dec_1_axi_m_wlast;
  logic                                  o_dec_1_axi_m_wvalid;
  logic                                  i_dec_1_axi_m_wready;
  /// AXI master 1 write response signals
  logic [      CODEC_AXI_RESP_WIDTH-1:0] i_dec_1_axi_m_bresp;
  logic [        CODEC_AXI_ID_WIDTH-1:0] i_dec_1_axi_m_bid;
  logic                                  i_dec_1_axi_m_bvalid;
  logic                                  o_dec_1_axi_m_bready;
  /// AXI master 1 read address signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] o_dec_1_axi_m_arid;
  logic [      CODEC_AXI_ADDR_WIDTH-1:0] o_dec_1_axi_m_araddr;
  logic [       CODEC_AXI_LEN_WIDTH-1:0] o_dec_1_axi_m_arlen;
  logic [      CODEC_AXI_SIZE_WIDTH-1:0] o_dec_1_axi_m_arsize;
  logic [      CODEC_AXI_PROT_WIDTH-1:0] o_dec_1_axi_m_arprot;
  logic [CODEC_AXI_BURST_TYPE_WIDTH-1:0] o_dec_1_axi_m_arburst;
  logic                                  o_dec_1_axi_m_arvalid;
  logic                                  i_dec_1_axi_m_arready;
  /// AXI master 1 read data signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] i_dec_1_axi_m_rid;
  logic [      CODEC_AXI_DATA_WIDTH-1:0] i_dec_1_axi_m_rdata;
  logic                                  i_dec_1_axi_m_rlast;
  logic                                  i_dec_1_axi_m_rvalid;
  logic [      CODEC_AXI_RESP_WIDTH-1:0] i_dec_1_axi_m_rresp;
  logic                                  o_dec_1_axi_m_rready;
  /// RISC-V interrupt signals
  logic                                  o_mcu_int_next;
  logic                                  i_mcu_ack_next;
  logic                                  i_mcu_int_prev;
  logic                                  o_mcu_ack_prev;
  /// RISC-V JTAG signals
  /// TODO:fix the naming convention
  logic                                  i_jtag_clk;
  logic                                  i_jtag_ms;
  logic                                  i_jtag_di;
  logic                                  o_jtag_do;
  /// RISC-V AXI master write address signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] o_mcu_axi_m_awid;
  logic [      CODEC_AXI_ADDR_WIDTH-1:0] o_mcu_axi_m_awaddr;
  logic [       CODEC_AXI_LEN_WIDTH-1:0] o_mcu_axi_m_awlen;
  logic [      CODEC_AXI_SIZE_WIDTH-1:0] o_mcu_axi_m_awsize;
  logic [      CODEC_AXI_PROT_WIDTH-1:0] o_mcu_axi_m_awprot;
  logic [CODEC_AXI_BURST_TYPE_WIDTH-1:0] o_mcu_axi_m_awburst;
  logic                                  o_mcu_axi_m_awvalid;
  logic                                  i_mcu_axi_m_awready;
  /// RISC-V AXI master write data signals
  logic [      CODEC_AXI_DATA_WIDTH-1:0] o_mcu_axi_m_wdata;
  logic [     CODEC_AXI_WSTRB_WIDTH-1:0] o_mcu_axi_m_wstrb;
  logic                                  o_mcu_axi_m_wlast;
  logic                                  o_mcu_axi_m_wvalid;
  logic                                  i_mcu_axi_m_wready;
  /// RISC-V AXI master write response signals
  logic [      CODEC_AXI_RESP_WIDTH-1:0] i_mcu_axi_m_bresp;
  logic [        CODEC_AXI_ID_WIDTH-1:0] i_mcu_axi_m_bid;
  logic                                  i_mcu_axi_m_bvalid;
  logic                                  o_mcu_axi_m_bready;
  /// RISC-V AXI master read address signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] o_mcu_axi_m_arid;
  logic [      CODEC_AXI_ADDR_WIDTH-1:0] o_mcu_axi_m_araddr;
  logic [       CODEC_AXI_LEN_WIDTH-1:0] o_mcu_axi_m_arlen;
  logic [      CODEC_AXI_SIZE_WIDTH-1:0] o_mcu_axi_m_arsize;
  logic [      CODEC_AXI_PROT_WIDTH-1:0] o_mcu_axi_m_arprot;
  logic [CODEC_AXI_BURST_TYPE_WIDTH-1:0] o_mcu_axi_m_arburst;
  logic                                  o_mcu_axi_m_arvalid;
  logic                                  i_mcu_axi_m_arready;
  /// RISC-V AXI master read data signals
  logic [        CODEC_AXI_ID_WIDTH-1:0] i_mcu_axi_m_rid;
  logic [      CODEC_AXI_DATA_WIDTH-1:0] i_mcu_axi_m_rdata;
  logic                                  i_mcu_axi_m_rlast;
  logic [      CODEC_AXI_RESP_WIDTH-1:0] i_mcu_axi_m_rresp;
  logic                                  i_mcu_axi_m_rvalid;
  logic                                  o_mcu_axi_m_rready;
  /// APB slave signals
  logic             i_cfg_apb4_s_paddr;
  logic            i_cfg_apb4_s_pwdata;
  logic                                  i_cfg_apb4_s_pwrite;
  logic                                  i_cfg_apb4_s_psel;
  logic                                  i_cfg_apb4_s_penable;
  logic             i_cfg_apb4_s_pstrb;
  logic [                           2:0] i_cfg_apb4_s_pprot;
  logic                                  o_cfg_apb4_s_pready;
  logic             o_cfg_apb4_s_prdata;
  logic                                  o_cfg_apb4_s_pslverr;
  /// decoder global signals
  logic                                  o_pintreq;
  logic [                          31:0] o_pintbus;
  /// DfT
  logic                                  i_test_mode;
  // SRAM configuration
  logic axe_tcl_sram_pkg::impl_inp_t     i_impl;
  logic axe_tcl_sram_pkg::impl_oup_t     o_impl;


  localparam int unsigned ResetCycles = 5;

  initial begin : proc_clk_rst_gen
    tb_clk   = 1'b0;
    tb_rst_n = 1'b0;
    fork
      begin : fork_clk_gen
        forever begin
          #(TbCycleTime/2);
          tb_clk = ~tb_clk;
        end
      end
      begin : fork_rst_gen
        repeat (ResetCycles) @(negedge tb_clk);
        tb_rst_n = 1'b1;
      end
    join
  end

  // Stimuli generation
  // TODO: Add some stimulies


  // Design Under Test (DUT)
  codec #(

  ) i_codec_dut (
    .i_clk                  (tb_clk),
    .i_rst_n                (tb_rst_n),
    .i_pclk                 (tb_pclk),
    .o_dec_0_axi_m_awid     (o_dec_0_axi_m_awid),
    .o_dec_0_axi_m_awaddr   (o_dec_0_axi_m_awaddr),
    .o_dec_0_axi_m_awlen    (o_dec_0_axi_m_awlen),
    .o_dec_0_axi_m_awsize   (o_dec_0_axi_m_awsize),
    .o_dec_0_axi_m_awprot   (o_dec_0_axi_m_awprot),
    .o_dec_0_axi_m_awburst  (o_dec_0_axi_m_awburst),
    .o_dec_0_axi_m_awvalid  (o_dec_0_axi_m_awvalid),
    .i_dec_0_axi_m_awready  (i_dec_0_axi_m_awready),
    .o_dec_0_axi_m_wdata    (o_dec_0_axi_m_wdata),
    .o_dec_0_axi_m_wstrb    (o_dec_0_axi_m_wstrb),
    .o_dec_0_axi_m_wlast    (o_dec_0_axi_m_wlast),
    .o_dec_0_axi_m_wvalid   (o_dec_0_axi_m_wvalid),
    .i_dec_0_axi_m_wready   (i_dec_0_axi_m_wready),
    .o_dec_0_axi_m_bready   (o_dec_0_axi_m_bready),
    .i_dec_0_axi_m_bvalid   (i_dec_0_axi_m_bvalid),
    .i_dec_0_axi_m_bresp    (i_dec_0_axi_m_bresp),
    .i_dec_0_axi_m_bid      (i_dec_0_axi_m_bid),
    .o_dec_0_axi_m_arid     (o_dec_0_axi_m_arid),
    .o_dec_0_axi_m_araddr   (o_dec_0_axi_m_araddr),
    .o_dec_0_axi_m_arlen    (o_dec_0_axi_m_arlen),
    .o_dec_0_axi_m_arsize   (o_dec_0_axi_m_arsize),
    .o_dec_0_axi_m_arprot   (o_dec_0_axi_m_arprot),
    .o_dec_0_axi_m_arburst  (o_dec_0_axi_m_arburst),
    .o_dec_0_axi_m_arvalid  (o_dec_0_axi_m_arvalid),
    .i_dec_0_axi_m_arready  (i_dec_0_axi_m_arready),
    .i_dec_0_axi_m_rid      (i_dec_0_axi_m_rid),
    .i_dec_0_axi_m_rdata    (i_dec_0_axi_m_rdata),
    .i_dec_0_axi_m_rlast    (i_dec_0_axi_m_rlast),
    .i_dec_0_axi_m_rvalid   (i_dec_0_axi_m_rvalid),
    .i_dec_0_axi_m_rresp    (i_dec_0_axi_m_rresp),
    .o_dec_0_axi_m_rready   (o_dec_0_axi_m_rready),
    .o_dec_1_axi_m_awid     (o_dec_1_axi_m_awid),
    .o_dec_1_axi_m_awaddr   (o_dec_1_axi_m_awaddr),
    .o_dec_1_axi_m_awlen    (o_dec_1_axi_m_awlen),
    .o_dec_1_axi_m_awsize   (o_dec_1_axi_m_awsize),
    .o_dec_1_axi_m_awprot   (o_dec_1_axi_m_awprot),
    .o_dec_1_axi_m_awburst  (o_dec_1_axi_m_awburst),
    .o_dec_1_axi_m_awvalid  (o_dec_1_axi_m_awvalid),
    .i_dec_1_axi_m_awready  (i_dec_1_axi_m_awready),
    .o_dec_1_axi_m_wdata    (o_dec_1_axi_m_wdata),
    .o_dec_1_axi_m_wstrb    (o_dec_1_axi_m_wstrb),
    .o_dec_1_axi_m_wlast    (o_dec_1_axi_m_wlast),
    .o_dec_1_axi_m_wvalid   (o_dec_1_axi_m_wvalid),
    .i_dec_1_axi_m_wready   (i_dec_1_axi_m_wready),
    .o_dec_1_axi_m_bready   (o_dec_1_axi_m_bready),
    .i_dec_1_axi_m_bvalid   (i_dec_1_axi_m_bvalid),
    .i_dec_1_axi_m_bresp    (i_dec_1_axi_m_bresp),
    .i_dec_1_axi_m_bid      (i_dec_1_axi_m_bid),
    .o_dec_1_axi_m_arid     (o_dec_1_axi_m_arid),
    .o_dec_1_axi_m_araddr   (o_dec_1_axi_m_araddr),
    .o_dec_1_axi_m_arlen    (o_dec_1_axi_m_arlen),
    .o_dec_1_axi_m_arsize   (o_dec_1_axi_m_arsize),
    .o_dec_1_axi_m_arprot   (o_dec_1_axi_m_arprot),
    .o_dec_1_axi_m_arburst  (o_dec_1_axi_m_arburst),
    .o_dec_1_axi_m_arvalid  (o_dec_1_axi_m_arvalid),
    .i_dec_1_axi_m_arready  (i_dec_1_axi_m_arready),
    .i_dec_1_axi_m_rid      (i_dec_1_axi_m_rid),
    .i_dec_1_axi_m_rdata    (i_dec_1_axi_m_rdata),
    .i_dec_1_axi_m_rlast    (i_dec_1_axi_m_rlast),
    .i_dec_1_axi_m_rvalid   (i_dec_1_axi_m_rvalid),
    .i_dec_1_axi_m_rresp    (i_dec_1_axi_m_rresp),
    .o_dec_1_axi_m_rready   (o_dec_1_axi_m_rready),
    .o_mcu_int_next         (o_mcu_int_next),
    .i_mcu_ack_next         (i_mcu_ack_next),
    .i_mcu_int_prev         (i_mcu_int_prev),
    .o_mcu_ack_prev         (o_mcu_ack_prev),
    .i_jtag_clk             (i_jtag_clk),
    .i_jtag_ms              (i_jtag_ms),
    .i_jtag_di              (i_jtag_di),
    .o_jtag_do              (o_jtag_do),
    .o_mcu_axi_m_awid       (o_mcu_axi_m_awid),
    .o_mcu_axi_m_awaddr     (o_mcu_axi_m_awaddr),
    .o_mcu_axi_m_awlen      (o_mcu_axi_m_awlen),
    .o_mcu_axi_m_awsize     (o_mcu_axi_m_awsize),
    .o_mcu_axi_m_awprot     (o_mcu_axi_m_awprot),
    .o_mcu_axi_m_awburst    (o_mcu_axi_m_awburst),
    .o_mcu_axi_m_awvalid    (o_mcu_axi_m_awvalid),
    .i_mcu_axi_m_awready    (i_mcu_axi_m_awready),
    .o_mcu_axi_m_wdata      (o_mcu_axi_m_wdata),
    .o_mcu_axi_m_wstrb      (o_mcu_axi_m_wstrb),
    .o_mcu_axi_m_wlast      (o_mcu_axi_m_wlast),
    .o_mcu_axi_m_wvalid     (o_mcu_axi_m_wvalid),
    .i_mcu_axi_m_wready     (i_mcu_axi_m_wready),
    .o_mcu_axi_m_bready     (o_mcu_axi_m_bready),
    .i_mcu_axi_m_bvalid     (i_mcu_axi_m_bvalid),
    .i_mcu_axi_m_bresp      (i_mcu_axi_m_bresp),
    .i_mcu_axi_m_bid        (i_mcu_axi_m_bid),
    .o_mcu_axi_m_arid       (o_mcu_axi_m_arid),
    .o_mcu_axi_m_araddr     (o_mcu_axi_m_araddr),
    .o_mcu_axi_m_arlen      (o_mcu_axi_m_arlen),
    .o_mcu_axi_m_arsize     (o_mcu_axi_m_arsize),
    .o_mcu_axi_m_arprot     (o_mcu_axi_m_arprot),
    .o_mcu_axi_m_arburst    (o_mcu_axi_m_arburst),
    .o_mcu_axi_m_arvalid    (o_mcu_axi_m_arvalid),
    .i_mcu_axi_m_arready    (i_mcu_axi_m_arready),
    .i_mcu_axi_m_rid        (i_mcu_axi_m_rid),
    .i_mcu_axi_m_rdata      (i_mcu_axi_m_rdata),
    .i_mcu_axi_m_rlast      (i_mcu_axi_m_rlast),
    .i_mcu_axi_m_rvalid     (i_mcu_axi_m_rvalid),
    .i_mcu_axi_m_rresp      (i_mcu_axi_m_rresp),
    .o_mcu_axi_m_rready     (o_mcu_axi_m_rready),
    .i_cfg_apb4_s_paddr (i_cfg_apb4_s_paddr),
    .i_cfg_apb4_s_pwdata  (i_cfg_apb4_s_pwdata),
    .i_cfg_apb4_s_pwrite  (i_cfg_apb4_s_pwrite),
    .i_cfg_apb4_s_psel  (i_cfg_apb4_s_psel),
    .i_cfg_apb4_s_penable (i_cfg_apb4_s_penable),
    .i_cfg_apb4_s_pstrb (i_cfg_apb4_s_pstrb),
    .i_cfg_apb4_s_pprot (i_cfg_apb4_s_pprot),
    .o_cfg_apb4_s_pready  (o_cfg_apb4_s_pready),
    .o_cfg_apb4_s_prdata  (o_cfg_apb4_s_prdata),
    .o_cfg_apb4_s_pslverr (o_cfg_apb4_s_pslverr)
  );

endmodule
