// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger memory
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module timestamp_logger_mem_arb #(
  parameter  int unsigned AxiIdWidth   = 4,
  parameter  int unsigned AxiAddrWidth = 36,
  parameter  int unsigned AxiDataWidth = 64,

  parameter  int unsigned MemoryWidth  = 64,
  parameter  int unsigned MemoryDepth  = 1024,
  parameter  int unsigned AddrCapacity = 'h1000,

  localparam type axi_id_t   = logic[AxiIdWidth      -1:0],
  localparam type axi_addr_t = logic[AxiAddrWidth    -1:0],
  localparam type axi_data_t = logic[AxiDataWidth    -1:0],
  localparam type axi_strb_t = logic[(AxiDataWidth/8)-1:0],

  localparam int unsigned MemAddrWidth = $clog2(MemoryDepth)
)(
  input  wire i_clk,
  input  wire i_rst_n,

  ///// AXI slave:
  // Write Address Channel
  input  axi_id_t             i_axi_s_aw_id,
  input  axi_addr_t           i_axi_s_aw_addr,
  input  axi_pkg::axi_len_t   i_axi_s_aw_len,
  input  axi_pkg::axi_size_t  i_axi_s_aw_size,
  input  axi_pkg::axi_burst_t i_axi_s_aw_burst,
  input  logic                i_axi_s_aw_valid,
  output logic                o_axi_s_aw_ready,
  // Write  Data Channel
  input  axi_data_t           i_axi_s_w_data,
  input  axi_strb_t           i_axi_s_w_strb,
  input  logic                i_axi_s_w_last,
  input  logic                i_axi_s_w_valid,
  output logic                o_axi_s_w_ready,
  // Write Response Channel
  output axi_id_t             o_axi_s_b_id,
  output axi_pkg::axi_resp_t  o_axi_s_b_resp,
  output logic                o_axi_s_b_valid,
  input  logic                i_axi_s_b_ready,
  // Read Address Channel
  input  axi_id_t             i_axi_s_ar_id,
  input  axi_addr_t           i_axi_s_ar_addr,
  input  axi_pkg::axi_len_t   i_axi_s_ar_len,
  input  axi_pkg::axi_size_t  i_axi_s_ar_size,
  input  axi_pkg::axi_burst_t i_axi_s_ar_burst,
  input  logic                i_axi_s_ar_valid,
  output logic                o_axi_s_ar_ready,
  // Read Data Channel
  output axi_id_t             o_axi_s_r_id,
  output axi_data_t           o_axi_s_r_data,
  output axi_pkg::axi_resp_t  o_axi_s_r_resp,
  output logic                o_axi_s_r_last,
  output logic                o_axi_s_r_valid,
  input  logic                i_axi_s_r_ready,

  // Logger connection
  input  logic                    i_log_req_valid,
  output logic                    o_log_req_ready,
  input  logic [MemoryWidth -1:0] i_log_req_data,
  input  logic [MemAddrWidth-1:0] i_log_req_addr_row,
  output logic                    o_log_rsp_valid,
  input  logic                    i_log_rsp_ready,

  // Ext rd connection
  input  logic                    i_ext_req_valid,
  output logic                    o_ext_req_ready,
  input  logic [MemAddrWidth-1:0] i_ext_req_addr_row,
  output logic                    o_ext_rsp_valid,
  input  logic                    i_ext_rsp_ready,
  output logic [MemoryWidth -1:0] o_ext_rsp_data,

  ///// Memory output:
  output logic                    o_ram_we,
  output logic                    o_ram_re,
  output logic [MemAddrWidth-1:0] o_ram_addr,
  output logic [MemoryWidth -1:0] o_ram_wdata,
  input  logic [MemoryWidth -1:0] i_ram_rdata
);

  localparam int unsigned AddrW = $clog2(AddrCapacity);
  localparam int unsigned RowAddrW = AddrW - $clog2(MemoryWidth/8);

  typedef struct packed {
    logic                    we;
    logic [RowAddrW-1:0]     row_addr;
    logic [MemoryWidth -1:0] data;
  } arb_req_t;

  typedef struct packed {
    logic                    error;
    logic [MemoryWidth -1:0] data;
  } arb_rsp_t;

  /// AXI2REG:
  logic      axi2reg_wvld, axi2reg_wrdy, axi2reg_wresp_vld, axi2reg_wresp_rdy;
  logic      axi2reg_rvld, axi2reg_rrdy, axi2reg_rresp_vld, axi2reg_rresp_rdy;
  logic      axi2reg_wresp_error, axi2reg_rresp_error;
  axi_data_t axi2reg_rresp_data;
  axi_data_t axi2reg_wdata;
  axi_addr_t axi2reg_waddr;
  axi_strb_t axi2reg_wstrb;
  axi_addr_t axi2reg_raddr;

  logic addr_err;
  reg addr_err_q;

  arb_req_t a2r_w_req, a2r_r_req, log_req, ext_req, arb_req;
  arb_rsp_t a2r_w_rsp, a2r_r_rsp, log_rsp, ext_rsp, arb_rsp;
  logic arb_req_vld, arb_req_rdy, arb_rsp_vld, arb_rsp_rdy;

  logic arb_req_vld_q;

  timestamp_logger_str_arb_resp #(
    .NumOutstanding(3),
    .req_data_t    (arb_req_t),
    .rsp_data_t    (arb_rsp_t),
    .NrSubs        (4),
    .Priority      (0)
  ) u_arb (
    .i_clk,
    .i_rst_n,

    .i_req_vld({i_ext_req_valid, axi2reg_wvld, axi2reg_rvld, i_log_req_valid}),
    .o_req_rdy({o_ext_req_ready, axi2reg_wrdy, axi2reg_rrdy, o_log_req_ready}),
    .i_req_data({ext_req, a2r_w_req, a2r_r_req, log_req}),
    .o_resp_vld({o_ext_rsp_valid, axi2reg_wresp_vld, axi2reg_rresp_vld, o_log_rsp_valid}),
    .i_resp_rdy({i_ext_rsp_ready, axi2reg_wresp_rdy, axi2reg_rresp_rdy, i_log_rsp_ready}),
    .o_resp_data({ext_rsp, a2r_w_rsp, a2r_r_rsp, log_rsp}),

    .o_req_vld(arb_req_vld),
    .i_req_rdy(arb_req_rdy),
    .o_req_data(arb_req),
    .i_resp_vld(arb_rsp_vld),
    .o_resp_rdy(arb_rsp_rdy),
    .i_resp_data(arb_rsp)
  );

  always_ff @(posedge i_clk, negedge i_rst_n) begin : i_mem_vld_reg
    if (i_rst_n == 1'b0) begin
      arb_req_vld_q <= '0;
      addr_err_q   <= '0;
    end else begin
      if ((arb_req_vld | arb_req_vld_q) & arb_rsp_rdy) begin
        arb_req_vld_q <= arb_req_vld;
        addr_err_q    <= addr_err;
      end
    end
  end

  // wire the request and response structs:
  always_comb a2r_w_req = arb_req_t'{
                                      we       : 1'b1,
                                      row_addr : axi2reg_waddr[$clog2(MemoryWidth/8)+:RowAddrW],
                                      data     : axi2reg_wdata
                                    };
  always_comb a2r_r_req = arb_req_t'{
                                      we       : 1'b0,
                                      row_addr : axi2reg_raddr[$clog2(MemoryWidth/8)+:RowAddrW],
                                      data     : MemoryWidth'(0)
                                    };
  always_comb log_req = arb_req_t'{
                                      we       : 1'b1,
                                      row_addr : i_log_req_addr_row,
                                      data     : i_log_req_data
                                    };
  always_comb ext_req = arb_req_t'{
                                      we       : 1'b0,
                                      row_addr : i_ext_req_addr_row,
                                      data     : MemoryWidth'(0)
                                    };
  always_comb axi2reg_wresp_error = a2r_w_rsp.error;
  always_comb axi2reg_rresp_error = a2r_r_rsp.error;
  always_comb axi2reg_rresp_data  = a2r_r_rsp.data;
  always_comb o_ext_rsp_data      = ext_rsp.data;

  always_comb o_ram_we = arb_req.we    & arb_req_vld & ~addr_err;
  always_comb o_ram_re = (~arb_req.we) & arb_req_vld & ~addr_err;
  always_comb o_ram_addr = arb_req.row_addr[MemAddrWidth-1:0];
  always_comb o_ram_wdata = arb_req.data;
  always_comb arb_rsp = arb_rsp_t'{
                                    error : addr_err_q,
                                    data  : i_ram_rdata
                                  };
  always_comb arb_rsp_vld = arb_req_vld_q;
  always_comb arb_req_rdy    = arb_rsp_rdy;

  // check if address is in capacity:
  if (AddrCapacity > (MemoryDepth * 8)) begin : g_addr_err_chk
    always_comb begin : addr_chk
      addr_err = 1'b0;

      if (|arb_req.row_addr[RowAddrW-1:MemAddrWidth])  // bits out of bit range
        addr_err = 1'b1;
    end
  end else begin : g_no_addr_err_chk
    always_comb addr_err = '0;
  end

  //////// AXI 2 REG, convert AXI to simple alligned single access
  axi2reg #(
    .IDW          (AxiIdWidth),
    .AW           (AxiAddrWidth),
    .DW           (AxiDataWidth),
    .BW           (axi_pkg::AXI_LEN_WIDTH),
    .NR_WR_REQS   (4),
    .NR_RD_REQS   (4),
    .WBUF         (2),
    .RD_RESP_DEPTH(2),
    .WR_RESP_DEPTH(2),
    .OSR          (3)
  ) u_axi_reg (
    .i_clk,
    .i_rst_n,

    ///// AXI slave:
    // Write Address Channel
    .awid           (i_axi_s_aw_id),
    .awaddr         (i_axi_s_aw_addr),
    .awlen          (i_axi_s_aw_len),
    .awsize         (i_axi_s_aw_size),
    .awburst        (i_axi_s_aw_burst),
    .awvalid        (i_axi_s_aw_valid),
    .awready        (o_axi_s_aw_ready),
    // Read Address Channel
    .arid           (i_axi_s_ar_id),
    .araddr         (i_axi_s_ar_addr),
    .arlen          (i_axi_s_ar_len),
    .arsize         (i_axi_s_ar_size),
    .arburst        (i_axi_s_ar_burst),
    .arvalid        (i_axi_s_ar_valid),
    .arready        (o_axi_s_ar_ready),
    // Write  Data Channel
    .wdata          (i_axi_s_w_data),
    .wstrb          (i_axi_s_w_strb),
    .wlast          (i_axi_s_w_last),
    .wvalid         (i_axi_s_w_valid),
    .wready         (o_axi_s_w_ready),
    // Read Data Channel
    .rid            (o_axi_s_r_id),
    .rdata          (o_axi_s_r_data),
    .rresp          (o_axi_s_r_resp),
    .rlast          (o_axi_s_r_last),
    .rvalid         (o_axi_s_r_valid),
    .rready         (i_axi_s_r_ready),
    // Write Response Channel
    .bid            (o_axi_s_b_id),
    .bresp          (o_axi_s_b_resp),
    .bvalid         (o_axi_s_b_valid),
    .bready         (i_axi_s_b_ready),

    ////// reg master:
    // Write path:
    .reg_wvld       (axi2reg_wvld),
    .reg_wrdy       (axi2reg_wrdy),
    .reg_waddr      (axi2reg_waddr),
    .reg_wdata      (axi2reg_wdata),
    .reg_wstrb      (axi2reg_wstrb),
    .reg_wresp_vld  (axi2reg_wresp_vld),
    .reg_wresp_rdy  (axi2reg_wresp_rdy),
    .reg_wresp_error(axi2reg_wresp_error),

    // Read path:
    .reg_rvld       (axi2reg_rvld),
    .reg_rrdy       (axi2reg_rrdy),
    .reg_raddr      (axi2reg_raddr),
    .reg_rresp_vld  (axi2reg_rresp_vld),
    .reg_rresp_rdy  (axi2reg_rresp_rdy),
    .reg_rresp_error(axi2reg_rresp_error),
    .reg_rresp_data (axi2reg_rresp_data)
  );
endmodule
