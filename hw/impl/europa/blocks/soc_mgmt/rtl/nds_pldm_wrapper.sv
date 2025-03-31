// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Debugger wrapper
// Owner: Joao Martins <joao.martins@axelera.ai>

module nds_pldm_wrapper #(
  // Provided to IP
  parameter int unsigned ADDR_WIDTH = 32,
  parameter int unsigned DATA_WIDTH = 32,
  parameter int unsigned SYS_ADDR_WIDTH = 32,
  parameter int unsigned SYS_DATA_WIDTH = 32,

  parameter int unsigned NHART = 1,
  parameter int unsigned DTM_ADDR_WIDTH = 9,

  parameter int unsigned RV_ID_WIDTH = 4,
  parameter int unsigned SYS_ID_WIDTH = 4,
  parameter int unsigned SYNC_STAGE = 2,
  parameter int unsigned SERIAL_COUNT = 0,
  parameter int unsigned SERIAL0 = 0,
  parameter int unsigned PROGBUF_SIZE = 2,
  parameter int unsigned HALTGROUP_COUNT = 0,
  parameter int unsigned DMXTRIGGER_COUNT = 0,
  parameter int unsigned NEXTDM_ADDR = 32'h0,

  parameter bit SYSTEM_BUS_ACCESS_SUPPORT = 1'b0,
  parameter bit RESUMEGROUP_SUPPORT = (DMXTRIGGER_COUNT > 0) ? 1'b1 : 1'b0,
  parameter bit HASEL_SUPPORT = 1'b1,

  // Not present in IP
  parameter int unsigned DMXTRIGGER_MSB = (DMXTRIGGER_COUNT > 0) ? DMXTRIGGER_COUNT - 1 : 0
)(
  input  wire i_clk,
  output wire o_ndmreset,
  input  wire i_dmi_resetn,
  input  wire i_bus_resetn,

  output logic [NHART-1:0] o_debugint,
  output logic [NHART-1:0] o_resethaltreq,
  output logic             o_dmactive,
  input  logic [NHART-1:0] i_hart_nonexistent,
  input  logic [NHART-1:0] i_hart_unavail,
  input  logic [NHART-1:0] i_hart_under_reset,

  // RV AXI
  input  logic [RV_ID_WIDTH-1:0]    i_rv_awid,
  input  logic [ADDR_WIDTH-1:0]     i_rv_awaddr,
  input  logic [7:0]                i_rv_awlen,
  input  logic [2:0]                i_rv_awsize,
  input  logic [1:0]                i_rv_awburst,
  input  logic                      i_rv_awlock,
  input  logic [3:0]                i_rv_awcache,
  input  logic [2:0]                i_rv_awprot,
  input  logic                      i_rv_awvalid,
  output logic                      o_rv_awready,
  input  logic [DATA_WIDTH-1:0]     i_rv_wdata,
  input  logic [(DATA_WIDTH/8)-1:0] i_rv_wstrb,
  input  logic                      i_rv_wlast,
  input  logic                      i_rv_wvalid,
  output logic                      o_rv_wready,
  output logic [RV_ID_WIDTH-1:0]    o_rv_bid,
  output logic [1:0]                o_rv_bresp,
  output logic                      o_rv_bvalid,
  input  logic                      i_rv_bready,
  input  logic [RV_ID_WIDTH-1:0]    i_rv_arid,
  input  logic [ADDR_WIDTH-1:0]     i_rv_araddr,
  input  logic [7:0]                i_rv_arlen,
  input  logic [2:0]                i_rv_arsize,
  input  logic [1:0]                i_rv_arburst,
  input  logic                      i_rv_arlock,
  input  logic [3:0]                i_rv_arcache,
  input  logic [2:0]                i_rv_arprot,
  input  logic                      i_rv_arvalid,
  output logic                      o_rv_arready,
  output logic [RV_ID_WIDTH-1:0]    o_rv_rid,
  output logic [DATA_WIDTH-1:0]     o_rv_rdata,
  output logic [1:0]                o_rv_rresp,
  output logic                      o_rv_rlast,
  output logic                      o_rv_rvalid,
  input  logic                      i_rv_rready,

  // SYS AXI IF
  output logic [SYS_ID_WIDTH-1:0]        o_sys_awid,
  output logic [SYS_ADDR_WIDTH-1:0]      o_sys_awaddr,
  output logic [7:0]                     o_sys_awlen,
  output logic [2:0]                     o_sys_awsize,
  output logic [1:0]                     o_sys_awburst,
  output logic                           o_sys_awlock,
  output logic [3:0]                     o_sys_awcache,
  output logic [2:0]                     o_sys_awprot,
  output logic                           o_sys_awvalid,
  input  logic                           i_sys_awready,
  output logic [SYS_DATA_WIDTH-1:0]      o_sys_wdata,
  output logic [(SYS_DATA_WIDTH/8)-1:0]  o_sys_wstrb,
  output logic                           o_sys_wlast,
  output logic                           o_sys_wvalid,
  input  logic                           i_sys_wready,
  input  logic [SYS_ID_WIDTH-1:0]        i_sys_bid,
  input  logic [1:0]                     i_sys_bresp,
  input  logic                           i_sys_bvalid,
  output logic                           o_sys_bready,
  output logic [SYS_ID_WIDTH-1:0]        o_sys_arid,
  output logic [SYS_ADDR_WIDTH-1:0]      o_sys_araddr,
  output logic [7:0]                     o_sys_arlen,
  output logic [2:0]                     o_sys_arsize,
  output logic [1:0]                     o_sys_arburst,
  output logic                           o_sys_arlock,
  output logic [3:0]                     o_sys_arcache,
  output logic [2:0]                     o_sys_arprot,
  output logic                           o_sys_arvalid,
  input  logic                           i_sys_arready,
  input  logic [SYS_ID_WIDTH-1:0]        i_sys_rid,
  input  logic [SYS_DATA_WIDTH-1:0]      i_sys_rdata,
  input  logic [1:0]                     i_sys_rresp,
  input  logic                           i_sys_rlast,
  input  logic                           i_sys_rvalid,
  output logic                           o_sys_rready,

  // DMI IF
  input  logic [DTM_ADDR_WIDTH-1:0] i_dmi_haddr,
  input  logic [1:0]                i_dmi_htrans,
  input  logic                      i_dmi_hwrite,
  input  logic [2:0]                i_dmi_hsize,
  input  logic [2:0]                i_dmi_hburst,
  input  logic [3:0]                i_dmi_hprot,
  input  logic [31:0]               i_dmi_hwdata,
  input  logic                      i_dmi_hsel,
  input  logic                      i_dmi_hready,
  output logic  [31:0]              o_dmi_hrdata,
  output logic                      o_dmi_hreadyout,
  output logic  [1:0]               o_dmi_hresp,

  // Triggers
  input  logic [DMXTRIGGER_MSB:0] i_xtrigger_halt_in,
  output logic [DMXTRIGGER_MSB:0] o_xtrigger_halt_out,
  input  logic [DMXTRIGGER_MSB:0] i_xtrigger_resume_in,
  output logic [DMXTRIGGER_MSB:0] o_xtrigger_resume_out
);

  // - Unused wiring
  // RV AHB
  logic [ADDR_WIDTH-1:0]     i_unused_rv_haddr;
  logic [1:0]                i_unused_rv_htrans;
  logic                      i_unused_rv_hwrite;
  logic [2:0]                i_unused_rv_hsize;
  logic [2:0]                i_unused_rv_hburst;
  logic [3:0]                i_unused_rv_hprot;
  logic [DATA_WIDTH-1:0]     i_unused_rv_hwdata;
  logic                      i_unused_rv_hsel;
  logic                      i_unused_rv_hready;
  logic [DATA_WIDTH-1:0]     o_unused_rv_hrdata;
  logic                      o_unused_rv_hreadyout;
  logic [1:0]                o_unused_rv_hresp;

  // SYS AHB IF
  logic [SYS_ADDR_WIDTH-1:0] o_unused_sys_haddr;
  logic [1:0]                o_unused_sys_htrans;
  logic                      o_unused_sys_hwrite;
  logic [2:0]                o_unused_sys_hsize;
  logic [2:0]                o_unused_sys_hburst;
  logic [3:0]                o_unused_sys_hprot;
  logic [SYS_DATA_WIDTH-1:0] o_unused_sys_hwdata;
  logic                      o_unused_sys_hbusreq;
  logic [SYS_DATA_WIDTH-1:0] i_unused_sys_hrdata;
  logic                      i_unused_sys_hready;
  logic [1:0]                i_unused_sys_hresp;
  logic                      i_unused_sys_hgrant;

  always_comb i_unused_rv_haddr   = {ADDR_WIDTH{1'b0}};
  always_comb i_unused_rv_htrans  = 2'd0;
  always_comb i_unused_rv_hwrite  = 1'b0;
  always_comb i_unused_rv_hsize   = 3'd0;
  always_comb i_unused_rv_hburst  = 3'd0;
  always_comb i_unused_rv_hprot   = 4'd0;
  always_comb i_unused_rv_hwdata  = {DATA_WIDTH{1'b0}};
  always_comb i_unused_rv_hsel    = 1'b0;
  always_comb i_unused_rv_hready  = 1'b0;
  always_comb i_unused_sys_hrdata = {SYS_DATA_WIDTH{1'b0}};
  always_comb i_unused_sys_hready = 1'b0;
  always_comb i_unused_sys_hresp  = 2'd0;
  always_comb i_unused_sys_hgrant = 1'b0;

  // - IP Instance
  ncepldm200 # (
    .ADDR_WIDTH                (ADDR_WIDTH),
    .DATA_WIDTH                (DATA_WIDTH),
    .SYS_ADDR_WIDTH            (SYS_ADDR_WIDTH),
    .SYS_DATA_WIDTH            (SYS_DATA_WIDTH),
    .NHART                     (NHART),
    .DTM_ADDR_WIDTH            (DTM_ADDR_WIDTH),
    .SYSTEM_BUS_ACCESS_SUPPORT (SYSTEM_BUS_ACCESS_SUPPORT ? "yes" : "no"),
    .RV_BUS_TYPE               ("axi"),
    .SYS_BUS_TYPE              ("axi"),
    .RV_ID_WIDTH               (RV_ID_WIDTH),
    .SYS_ID_WIDTH              (SYS_ID_WIDTH),
    .SYNC_STAGE                (SYNC_STAGE),
    .SERIAL_COUNT              (SERIAL_COUNT),
    .SERIAL0                   (SERIAL0),
    .PROGBUF_SIZE              (PROGBUF_SIZE),
    .HALTGROUP_COUNT           (HALTGROUP_COUNT),
    .DMXTRIGGER_COUNT          (DMXTRIGGER_COUNT),
    .RESUMEGROUP_SUPPORT       (RESUMEGROUP_SUPPORT ? "yes" : "no"),
    .HASEL_SUPPORT             (HASEL_SUPPORT ? "yes" : "no"),
    .NEXTDM_ADDR               (NEXTDM_ADDR)
    ) u_ncepldm200 (
      .clk(i_clk),
      .ndmreset(o_ndmreset),
      .dmi_resetn(i_dmi_resetn),
      .bus_resetn(i_bus_resetn),

      .debugint(o_debugint),
      .resethaltreq(o_resethaltreq),
      .dmactive(o_dmactive),
      .hart_nonexistent(i_hart_nonexistent),
      .hart_unavail(i_hart_unavail),
      .hart_under_reset(i_hart_under_reset),

      // RV AXI
      .rv_awid(i_rv_awid),
      .rv_awaddr(i_rv_awaddr),
      .rv_awlen(i_rv_awlen),
      .rv_awsize(i_rv_awsize),
      .rv_awburst(i_rv_awburst),
      .rv_awlock(i_rv_awlock),
      .rv_awcache(i_rv_awcache),
      .rv_awprot(i_rv_awprot),
      .rv_awvalid(i_rv_awvalid),
      .rv_awready(o_rv_awready),
      .rv_wdata(i_rv_wdata),
      .rv_wstrb(i_rv_wstrb),
      .rv_wlast(i_rv_wlast),
      .rv_wvalid(i_rv_wvalid),
      .rv_wready(o_rv_wready),
      .rv_bid(o_rv_bid),
      .rv_bresp(o_rv_bresp),
      .rv_bvalid(o_rv_bvalid),
      .rv_bready(i_rv_bready),
      .rv_arid(i_rv_arid),
      .rv_araddr(i_rv_araddr),
      .rv_arlen(i_rv_arlen),
      .rv_arsize(i_rv_arsize),
      .rv_arburst(i_rv_arburst),
      .rv_arlock(i_rv_arlock),
      .rv_arcache(i_rv_arcache),
      .rv_arprot(i_rv_arprot),
      .rv_arvalid(i_rv_arvalid),
      .rv_arready(o_rv_arready),
      .rv_rid(o_rv_rid),
      .rv_rdata(o_rv_rdata),
      .rv_rresp(o_rv_rresp),
      .rv_rlast(o_rv_rlast),
      .rv_rvalid(o_rv_rvalid),
      .rv_rready(i_rv_rready),

      // SYS AXI IF
      .sys_awid(o_sys_awid),
      .sys_awaddr(o_sys_awaddr),
      .sys_awlen(o_sys_awlen),
      .sys_awsize(o_sys_awsize),
      .sys_awburst(o_sys_awburst),
      .sys_awlock(o_sys_awlock),
      .sys_awcache(o_sys_awcache),
      .sys_awprot(o_sys_awprot),
      .sys_awvalid(o_sys_awvalid),
      .sys_awready(i_sys_awready),
      .sys_wdata(o_sys_wdata),
      .sys_wstrb(o_sys_wstrb),
      .sys_wlast(o_sys_wlast),
      .sys_wvalid(o_sys_wvalid),
      .sys_wready(i_sys_wready),
      .sys_bid(i_sys_bid),
      .sys_bresp(i_sys_bresp),
      .sys_bvalid(i_sys_bvalid),
      .sys_bready(o_sys_bready),
      .sys_arid(o_sys_arid),
      .sys_araddr(o_sys_araddr),
      .sys_arlen(o_sys_arlen),
      .sys_arsize(o_sys_arsize),
      .sys_arburst(o_sys_arburst),
      .sys_arlock(o_sys_arlock),
      .sys_arcache(o_sys_arcache),
      .sys_arprot(o_sys_arprot),
      .sys_arvalid(o_sys_arvalid),
      .sys_arready(i_sys_arready),
      .sys_rid(i_sys_rid),
      .sys_rdata(i_sys_rdata),
      .sys_rresp(i_sys_rresp),
      .sys_rlast(i_sys_rlast),
      .sys_rvalid(i_sys_rvalid),
      .sys_rready(o_sys_rready),

      // DMI IF
      .dmi_haddr(i_dmi_haddr),
      .dmi_htrans(i_dmi_htrans),
      .dmi_hwrite(i_dmi_hwrite),
      .dmi_hsize(i_dmi_hsize),
      .dmi_hburst(i_dmi_hburst),
      .dmi_hprot(i_dmi_hprot),
      .dmi_hwdata(i_dmi_hwdata),
      .dmi_hsel(i_dmi_hsel),
      .dmi_hready(i_dmi_hready),
      .dmi_hrdata(o_dmi_hrdata),
      .dmi_hreadyout(o_dmi_hreadyout),
      .dmi_hresp(o_dmi_hresp),

      // Triggers
      .xtrigger_halt_in(i_xtrigger_halt_in),
      .xtrigger_halt_out(o_xtrigger_halt_out),
      .xtrigger_resume_in(i_xtrigger_resume_in),
      .xtrigger_resume_out(o_xtrigger_resume_out),

      // -- UNUSED IO
      // RV AHB
      .rv_haddr    (i_unused_rv_haddr),
      .rv_htrans   (i_unused_rv_htrans),
      .rv_hwrite   (i_unused_rv_hwrite),
      .rv_hsize    (i_unused_rv_hsize),
      .rv_hburst   (i_unused_rv_hburst),
      .rv_hprot    (i_unused_rv_hprot),
      .rv_hwdata   (i_unused_rv_hwdata),
      .rv_hsel     (i_unused_rv_hsel),
      .rv_hready   (i_unused_rv_hready),
      .rv_hrdata   (o_unused_rv_hrdata),
      .rv_hreadyout(o_unused_rv_hreadyout),
      .rv_hresp    (o_unused_rv_hresp),

      // SYS AHB IF
      .sys_haddr   (o_unused_sys_haddr),
      .sys_htrans  (o_unused_sys_htrans),
      .sys_hwrite  (o_unused_sys_hwrite),
      .sys_hsize   (o_unused_sys_hsize),
      .sys_hburst  (o_unused_sys_hburst),
      .sys_hprot   (o_unused_sys_hprot),
      .sys_hwdata  (o_unused_sys_hwdata),
      .sys_hbusreq (o_unused_sys_hbusreq),
      .sys_hrdata  (i_unused_sys_hrdata),
      .sys_hready  (i_unused_sys_hready),
      .sys_hresp   (i_unused_sys_hresp),
      .sys_hgrant  (i_unused_sys_hgrant)
  );

endmodule
