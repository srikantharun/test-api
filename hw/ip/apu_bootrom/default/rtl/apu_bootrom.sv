/// Description: Application Processor Unit Boot ROM
///
module apu_bootrom
  import apu_bootrom_pkg::*;
#(
  /// AXI ID width
  parameter int unsigned AxiIdWidth   = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// AXI Address width
  parameter int unsigned AxiAddrWidth = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// The number of parallel outstanding reads the boot ROM can do at a given time.
  parameter int unsigned AxiMaxReads  = 4,

  parameter type axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t,

  parameter ImplKey = "default",
  parameter type impl_inp_t = axe_tcl_sram_pkg::impl_inp_rom_t,
  parameter type impl_oup_t = axe_tcl_sram_pkg::impl_oup_rom_t
) (
  /// Clock, positive edge triggered
  input wire i_clk,
  /// Clock, positive edge triggered, synced with i_clk but without OCC
  input wire i_free_run_clk,
  /// Asynchronous reset, active low
  input wire i_rst_n,

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_aw_t i_axi_s_aw,
  input  logic    i_axi_s_aw_valid,
  output logic    o_axi_s_aw_ready,
  input  axi_w_t  i_axi_s_w,
  input  logic    i_axi_s_w_valid,
  output logic    o_axi_s_w_ready,
  output axi_b_t  o_axi_s_b,
  output logic    o_axi_s_b_valid,
  input  logic    i_axi_s_b_ready,
  input  axi_ar_t i_axi_s_ar,
  input  logic    i_axi_s_ar_valid,
  output logic    o_axi_s_ar_ready,
  output axi_r_t  o_axi_s_r,
  output logic    o_axi_s_r_valid,
  input  logic    i_axi_s_r_ready,

  /// Implementation specific sideband inputs
  input  impl_inp_t i_impl,
  /// Implementation specific sideband outputs
  output impl_oup_t o_impl
);

  if ($bits(o_axi_s_r.data) != APU_BOOTROM_DATA_W) $fatal(1, "'DataWidth' problem on `o_axi_s_r`;");
  if ($bits(i_axi_s_w.data) != APU_BOOTROM_DATA_W) $fatal(1, "'DataWidth' problem on `i_axi_s_w`;");

  // Drive ROM macro with 1 pulse out of 2 from i_clk
  logic clk_gate_enable;
  wire div_2_clk;

  always_ff @(posedge i_free_run_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      clk_gate_enable <= '0;
    end
    else begin
      clk_gate_enable <= ~clk_gate_enable;
    end
  end

  axe_tcl_clk_gating u_tcl_clk_gate (
    .i_clk(i_free_run_clk),
    .i_en(clk_gate_enable),
    .i_test_en('0),
    .o_clk(div_2_clk)
  );

  // axe_axi 64/AxiAddrWidth to reg 64/AxiAddrWidth
  typedef logic [AxiAddrWidth-1:0] bootrom_axi_addr_t;
  typedef logic [APU_BOOTROM_DATA_W-1:0] bootrom_data_t;

  logic              read_req;
  logic              read_data_vld;
  bootrom_axi_addr_t read_addr;
  bootrom_data_t     read_data;

  axi2reg #(
    .IDW          (AxiIdWidth),
    .AW           (AxiAddrWidth),
    .DW           (APU_BOOTROM_DATA_W),
    .BW           (axi_pkg::AXI_LEN_WIDTH),
    .NR_WR_REQS   (2),
    .NR_RD_REQS   (AxiMaxReads),
    .WBUF         (2),
    .RD_RESP_DEPTH(2),
    .WR_RESP_DEPTH(2),
    .OSR          (2)
  ) u_axi2reg_bootrom (
    .i_clk,
    .i_rst_n,
    ///// AXI slave:
    // Write Address Channel
    .awid   (i_axi_s_aw.id),
    .awaddr (i_axi_s_aw.addr),
    .awlen  (i_axi_s_aw.len),
    .awsize (i_axi_s_aw.size),
    .awburst(i_axi_s_aw.burst),
    .awvalid(i_axi_s_aw_valid),
    .awready(o_axi_s_aw_ready),
    // Read Address Channel
    .arid   (i_axi_s_ar.id),
    .araddr (i_axi_s_ar.addr),
    .arlen  (i_axi_s_ar.len),
    .arsize (i_axi_s_ar.size),
    .arburst(i_axi_s_ar.burst),
    .arvalid(i_axi_s_ar_valid),
    .arready(o_axi_s_ar_ready),
    // Write  Data Channel
    .wdata  (i_axi_s_w.data),
    .wstrb  (i_axi_s_w.strb),
    .wlast  (i_axi_s_w.last),
    .wvalid (i_axi_s_w_valid),
    .wready (o_axi_s_w_ready),
    // Read Data Channel
    .rid    (o_axi_s_r.id),
    .rdata  (o_axi_s_r.data),
    .rresp  (o_axi_s_r.resp[axi_pkg::AXI_RESP_WIDTH-1:0]),
    .rlast  (o_axi_s_r.last),
    .rvalid (o_axi_s_r_valid),
    .rready (i_axi_s_r_ready),
    // Write Response Channel
    .bid    (o_axi_s_b.id),
    .bresp  (o_axi_s_b.resp[axi_pkg::AXI_RESP_WIDTH-1:0]),
    .bvalid (o_axi_s_b_valid),
    .bready (i_axi_s_b_ready),
    ////// reg master:
    // Write path:
    .reg_wvld       (),
    .reg_wrdy       ('0),
    .reg_waddr      (),
    .reg_wdata      (),
    .reg_wstrb      (),
    .reg_wresp_vld  ('0),
    .reg_wresp_rdy  (),
    .reg_wresp_error('0),
    // Read path:
    .reg_rvld       (read_req),
    .reg_rrdy       (clk_gate_enable),
    .reg_raddr      (read_addr),
    .reg_rresp_vld  (clk_gate_enable & read_data_vld),
    .reg_rresp_rdy  (),
    .reg_rresp_error('0),
    .reg_rresp_data (read_data)
  );

  always_comb o_axi_s_b.user = '0;
  always_comb o_axi_s_r.user = '0;

  // ROM inst
  typedef logic [APU_BOOTROM_ADDR_W-1:0] bootrom_addr_t;

  bootrom_addr_t real_addr;

  // Truncate per word and wrap in case of out of bound
  always_comb real_addr = read_addr[APU_BOOTROM_ADDR_W+APU_BOOTROM_STRB_W-1:APU_BOOTROM_STRB_W];

  // Trust me the data will be valid the next cycle
  always_ff @(posedge div_2_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      read_data_vld <= '0;
    end
    else begin
      read_data_vld <= read_req;
    end
  end

  axe_tcl_rom_1p #(
    .NumWords(APU_BOOTROM_NUM_WORDS),
    .DataWidth(APU_BOOTROM_DATA_W),
    .ReadLatency(1),
    .ImplKey(ImplKey),
    .impl_inp_t(impl_inp_t),
    .impl_oup_t(impl_oup_t)
  ) u_rom (
    .i_clk(div_2_clk),
    .i_rst_n,

    .i_req(read_req),
    .i_addr(real_addr),
    .o_rd_data(read_data),

    .i_impl,
    .o_impl
  );

endmodule
