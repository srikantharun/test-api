/// Description: wrapper around Andes PLIC
///
module nds_plic_wrapper #(
  localparam int unsigned MAX_INTERRUPT_WIDTH = 1023,
  // 1:1023
  parameter  int unsigned INTERRUPT_WIDTH = 63,

  localparam int unsigned MAX_TARGET_WIDTH = 16,
  // 1:16
  parameter  int unsigned TARGET_WIDTH = 8,

  // 3 / 7 / 15 / 31 / 63 / 127 / 255
  parameter int unsigned MAX_PRIORITY = 15,

  // 1 bit per interrupt
  // 0: level-triggered
  // 1: edge-triggered
  parameter bit [MAX_INTERRUPT_WIDTH:0] EDGE_TRIGGER = 0,
  // 0: synchronous
  // 1: asynchronous
  parameter bit [MAX_INTERRUPT_WIDTH:0] ASYNC_INTERRUPT = 0,

  // TODO(@vincent.morillon): not documented by andes
  // 0: hardware interrupt
  // 1: software interrupt
  parameter bit PROGRAMMABLE_TRIGGER = 0,

  // 32 / 64
  parameter int unsigned AXI_DATA_WIDTH = 64,
  // >= 22
  parameter int unsigned AXI_ADDR_WIDTH = 40,
  // 4:32
  parameter int unsigned AXI_ID_WIDTH = 4
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic [INTERRUPT_WIDTH:1] i_interrupt_src,
  output logic [TARGET_WIDTH - 1:0] o_targets_eip,

  input logic [AXI_ADDR_WIDTH - 1:0] i_axi_s_araddr,
  input axi_pkg::axi_burst_e i_axi_s_arburst,
  input axi_pkg::axi_cache_t i_axi_s_arcache,
  input logic [AXI_ID_WIDTH - 1:0] i_axi_s_arid,
  input axi_pkg::axi_len_t i_axi_s_arlen,
  input logic i_axi_s_arlock,
  input axi_pkg::axi_prot_t i_axi_s_arprot,
  input axi_pkg::axi_size_e i_axi_s_arsize,
  output logic o_axi_s_arready,
  input logic i_axi_s_arvalid,
  input logic [AXI_ADDR_WIDTH - 1:0] i_axi_s_awaddr,
  input axi_pkg::axi_burst_e i_axi_s_awburst,
  input axi_pkg::axi_cache_t i_axi_s_awcache,
  input logic [AXI_ID_WIDTH - 1:0] i_axi_s_awid,
  input axi_pkg::axi_len_t i_axi_s_awlen,
  input logic i_axi_s_awlock,
  input axi_pkg::axi_prot_t i_axi_s_awprot,
  input axi_pkg::axi_size_e i_axi_s_awsize,
  output logic o_axi_s_awready,
  input logic i_axi_s_awvalid,
  output logic [AXI_ID_WIDTH - 1:0] o_axi_s_bid,
  output axi_pkg::axi_resp_e o_axi_s_bresp,
  input logic i_axi_s_bready,
  output logic o_axi_s_bvalid,
  output logic [AXI_DATA_WIDTH - 1:0] o_axi_s_rdata,
  output logic [AXI_ID_WIDTH - 1:0] o_axi_s_rid,
  output logic o_axi_s_rlast,
  output axi_pkg::axi_resp_e o_axi_s_rresp,
  input logic i_axi_s_rready,
  output logic o_axi_s_rvalid,
  input logic [AXI_DATA_WIDTH - 1:0] i_axi_s_wdata,
  input logic i_axi_s_wlast,
  input logic [(AXI_DATA_WIDTH / 8) - 1:0] i_axi_s_wstrb,
  output logic o_axi_s_wready,
  input logic i_axi_s_wvalid
);

  // [MAX_TARGET_WIDTH -1:TARGET_WIDTH] unused
  logic [MAX_TARGET_WIDTH - 1:0] targets_eip;
  always_comb begin
    foreach (o_targets_eip[i]) begin
      o_targets_eip[i] = targets_eip[i];
    end
  end

  // Unsupported vectored PLIC extension
  logic [MAX_TARGET_WIDTH - 1:0][9:0] unused_targets_eiid;

  // Unused AHB bus
  logic [AXI_DATA_WIDTH - 1:0] unused_ahb_s_hrdata;
  logic [1:0] unused_ahb_s_hresp;
  logic unused_ahb_s_hreadyout;

  // Workaround casting issue with enums
  axi_pkg::axi_resp_t axi_s_bresp;
  axi_pkg::axi_resp_t axi_s_rresp;
  assign o_axi_s_bresp = axi_pkg::axi_resp_e'(axi_s_bresp);
  assign o_axi_s_rresp = axi_pkg::axi_resp_e'(axi_s_rresp);

  nceplic100 #(
    .INT_NUM(INTERRUPT_WIDTH),
    .TARGET_NUM(TARGET_WIDTH),
    .MAX_PRIORITY(MAX_PRIORITY),
    .PROGRAMMABLE_TRIGGER(PROGRAMMABLE_TRIGGER),
    .EDGE_TRIGGER(EDGE_TRIGGER),
    .ASYNC_INT(ASYNC_INTERRUPT),
    .ADDR_WIDTH(AXI_ADDR_WIDTH),
    .DATA_WIDTH(AXI_DATA_WIDTH),
    .ID_WIDTH(AXI_ID_WIDTH)
  ) u_nceplic100 (
    .clk(i_clk),
    .reset_n(i_rst_n),
    .int_src(i_interrupt_src),
    .t0_eip(targets_eip[0]),
    .t1_eip(targets_eip[1]),
    .t2_eip(targets_eip[2]),
    .t3_eip(targets_eip[3]),
    .t4_eip(targets_eip[4]),
    .t5_eip(targets_eip[5]),
    .t6_eip(targets_eip[6]),
    .t7_eip(targets_eip[7]),
    .t8_eip(targets_eip[8]),
    .t9_eip(targets_eip[9]),
    .t10_eip(targets_eip[10]),
    .t11_eip(targets_eip[11]),
    .t12_eip(targets_eip[12]),
    .t13_eip(targets_eip[13]),
    .t14_eip(targets_eip[14]),
    .t15_eip(targets_eip[15]),
    .t0_eiid(unused_targets_eiid[0]),
    .t1_eiid(unused_targets_eiid[1]),
    .t2_eiid(unused_targets_eiid[2]),
    .t3_eiid(unused_targets_eiid[3]),
    .t4_eiid(unused_targets_eiid[4]),
    .t5_eiid(unused_targets_eiid[5]),
    .t6_eiid(unused_targets_eiid[6]),
    .t7_eiid(unused_targets_eiid[7]),
    .t8_eiid(unused_targets_eiid[8]),
    .t9_eiid(unused_targets_eiid[9]),
    .t10_eiid(unused_targets_eiid[10]),
    .t11_eiid(unused_targets_eiid[11]),
    .t12_eiid(unused_targets_eiid[12]),
    .t13_eiid(unused_targets_eiid[13]),
    .t14_eiid(unused_targets_eiid[14]),
    .t15_eiid(unused_targets_eiid[15]),
    .t0_eiack('0),
    .t1_eiack('0),
    .t2_eiack('0),
    .t3_eiack('0),
    .t4_eiack('0),
    .t5_eiack('0),
    .t6_eiack('0),
    .t7_eiack('0),
    .t8_eiack('0),
    .t9_eiack('0),
    .t10_eiack('0),
    .t11_eiack('0),
    .t12_eiack('0),
    .t13_eiack('0),
    .t14_eiack('0),
    .t15_eiack('0),
    .haddr('0),
    .hburst('0),
    .hrdata(unused_ahb_s_hrdata),
    .hresp(unused_ahb_s_hresp),
    .hsel('0),
    .hsize('0),
    .htrans('0),
    .hwdata('0),
    .hwrite('0),
    .hready('0),
    .hreadyout(unused_ahb_s_hreadyout),
    .araddr(i_axi_s_araddr),
    .arburst(i_axi_s_arburst),
    .arcache(i_axi_s_arcache),
    .arid(i_axi_s_arid),
    .arlen(i_axi_s_arlen),
    .arlock(i_axi_s_arlock),
    .arprot(i_axi_s_arprot),
    .arsize(i_axi_s_arsize),
    .arready(o_axi_s_arready),
    .arvalid(i_axi_s_arvalid),
    .awaddr(i_axi_s_awaddr),
    .awburst(i_axi_s_awburst),
    .awcache(i_axi_s_awcache),
    .awid(i_axi_s_awid),
    .awlen(i_axi_s_awlen),
    .awlock(i_axi_s_awlock),
    .awprot(i_axi_s_awprot),
    .awsize(i_axi_s_awsize),
    .awready(o_axi_s_awready),
    .awvalid(i_axi_s_awvalid),
    .bid(o_axi_s_bid),
    .bresp(axi_s_bresp),
    .bready(i_axi_s_bready),
    .bvalid(o_axi_s_bvalid),
    .rdata(o_axi_s_rdata),
    .rid(o_axi_s_rid),
    .rlast(o_axi_s_rlast),
    .rresp(axi_s_rresp),
    .rready(i_axi_s_rready),
    .rvalid(o_axi_s_rvalid),
    .wdata(i_axi_s_wdata),
    .wlast(i_axi_s_wlast),
    .wstrb(i_axi_s_wstrb),
    .wready(o_axi_s_wready),
    .wvalid(i_axi_s_wvalid)
  );

endmodule
