// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IFD ODR testbench, simple directed "test" moving data for visual inspection
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`include "axi_intf.sv"
`include "axis_driver.sv"

module ifd_odr_tb;
  import ifd_odr_pkg::*;
  import tb_axi_pkg::*;
  localparam AW = 40;
  localparam AXI_DW = 64;
  localparam IDW = 4;
  localparam BW = 6;

  localparam DW = 512;
  localparam PWORD_LEN = 64;
  localparam EL_DW = DW / PWORD_LEN;

  localparam TOK_PROD = 5;
  localparam TOK_CONS = 3;
  localparam BPCMD_W = 128;

  localparam PAYLOAD_W = ifd_odr_pkg::IFD_ODR_AG_CMD_DW;

  enum bit {
    PAD = 1'b1,
    NO_PAD = 1'b0
  } pad_t;
  enum bit {
    DROP = 1'b1,
    NO_DROP = 1'b0
  } drop_t;

  logic tb_clk;
  logic tb_rst_n;

  logic clk_req;

  //////// AXIS drivers
  axis_intf ifd_axis_if ();
  axis_intf odr_axis_if ();
  axis_driver ifd_axis_drv = new(ifd_axis_if, 0);  //slave
  axis_driver odr_axis_drv = new(odr_axis_if, 1);  //master
  mailbox mail_ifd_axis = new();
  mailbox mail_odr_axis = new();

  initial begin
    ifd_axis_drv.axis_in = mail_ifd_axis;
    odr_axis_drv.axis_out = mail_odr_axis;

    ifd_axis_drv.perc_stall_rdy = 20;
  end

  //////// AXI drivers
  axi_intf #(.DW(AXI_DW), .AW(AW)) ifd_axi_if ();
  axi_cmdblock_driver #(
    .DW(AXI_DW),
    .AW(AW),
    .DYN_CMD_W(PAYLOAD_W),
    .NR_FORMATS(ifd_odr_pkg::CMD_NR_FORMATS),
    .FORMAT_NR_BYTES(ifd_odr_pkg::IFD_ODR_CMDB_FORMAT_NR_BYTES)
  ) ifd_cmd_drv = new(
      "IFD_AXI", ifd_axi_if
  );

  axi_intf #(.DW(AXI_DW), .AW(AW)) odr_axi_if ();
  axi_cmdblock_driver #(
    .DW(AXI_DW),
    .AW(AW),
    .DYN_CMD_W(PAYLOAD_W),
    .NR_FORMATS(ifd_odr_pkg::CMD_NR_FORMATS),
    .FORMAT_NR_BYTES(ifd_odr_pkg::IFD_ODR_CMDB_FORMAT_NR_BYTES)
  ) odr_cmd_drv = new(
      "ODR_AXI", odr_axi_if
  );

  initial begin
    ifd_cmd_drv.set_csr_base('0);
    ifd_cmd_drv.set_cmd_base('0 + 'h1000);  // cmd
    ifd_cmd_drv.set_id(0);
    odr_cmd_drv.set_csr_base('0);  // csr
    odr_cmd_drv.set_cmd_base('0 + 'h1000);  // cmd
    odr_cmd_drv.set_id(2);
  end

  assign ifd_axi_if.clk = tb_clk;
  assign ifd_axi_if.rst_n = tb_rst_n;
  assign odr_axi_if.clk = tb_clk;
  assign odr_axi_if.rst_n = tb_rst_n;
  assign ifd_axis_if.clk = tb_clk;
  assign ifd_axis_if.rst_n = tb_rst_n;
  assign odr_axis_if.clk = tb_clk;
  assign odr_axis_if.rst_n = tb_rst_n;

  // MMIO:
  mmio_pkg::mmio_dmc_ro_req_t                ifd_mm_req;
  mmio_pkg::mmio_dmc_ro_rsp_t                ifd_mm_rsp;
  mmio_pkg::mmio_dmc_wo_req_t                odr_mm_req;
  mmio_pkg::mmio_dmc_wo_rsp_t                odr_mm_rsp;

  // ODR:
  // req:
  logic                [      AW-1:0] mm2_addr;
  logic                [      DW-1:0] mm2_wdata;
  logic                               mm2_we;
  logic                               mm2_vld;
  logic                               mm2_rdy;

  // resp:
  logic                [      DW-1:0] mm2_rdata;
  logic                               mm2_ack;

  //tokens
  logic                [TOK_PROD-1:0] ifd_tok_prod_rdy;
  logic                [TOK_PROD-1:0] ifd_tok_prod_vld;
  logic                [TOK_CONS-1:0] ifd_tok_cons_rdy;
  logic                [TOK_CONS-1:0] ifd_tok_cons_vld;
  logic                [TOK_PROD-1:0] odr_tok_prod_rdy;
  logic                [TOK_PROD-1:0] odr_tok_prod_vld;
  logic                [TOK_CONS-1:0] odr_tok_cons_rdy;
  logic                [TOK_CONS-1:0] odr_tok_cons_vld;

  // status and opt config
  logic                               last_rcvd;

`ifdef VCD_ENABLE
  integer f_vcdOn, f_vcdOff;

  initial begin
    f_vcdOn  = $fopen("vcdOnStamps.txt", "w");
    f_vcdOff = $fopen("vcdOffStamps.txt", "w");
  end

  task setDump;
    input string dump_filename;
    begin
      $dumpfile({dump_filename, ".vcd"});
      $dumpvars(0, tb_dma_top.my_dma);
      $dumpoff;
    end
  endtask

  task startVcdDump;
    begin
      $dumpon;
      $display("INFO: vcd dump on at %0t", $time);
      $fwrite(f_vcdOn, "%0t\n", $time);
    end
  endtask

  task stopVcdDump;
    begin
      $dumpoff;
      $display("INFO: vcd dump off at %0t", $time);
      $fwrite(f_vcdOff, "%0t\n", $time);
    end
  endtask
`endif

  // clock generation:
  initial begin
    tb_clk = 0;
    forever #((1.250) / 2) tb_clk = ~tb_clk;
  end

  // reset generation:
  initial begin
    tb_rst_n = 0;
    repeat (20) @(posedge tb_clk);
    #1;
    tb_rst_n = 1;
  end

  initial begin
    $display("RUN!");
    fork
      ifd_cmd_drv.run();
      odr_cmd_drv.run();
      ifd_axis_drv.run();
      odr_axis_drv.run();
    join
    $display("RUN! Done");
  end

  ////////////////////////////////////////////////////////
  // DUT:
  ifd #(
    .NR_TOK_PROD(TOK_PROD),
    .NR_TOK_CONS(TOK_CONS)
  ) i_ifd (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n),

    .irq(),

    // AXI slave:
    // write address channel:
    .awid(ifd_axi_if.awid),
    .awaddr(ifd_axi_if.awaddr),
    .awlen(ifd_axi_if.awlen),
    .awsize(ifd_axi_if.awsize),
    .awburst(ifd_axi_if.awburst),
    .awvalid(ifd_axi_if.awvalid),
    .awready(ifd_axi_if.awready),
    // read address channel:
    .arid(ifd_axi_if.arid),
    .araddr(ifd_axi_if.araddr),
    .arlen(ifd_axi_if.arlen),
    .arsize(ifd_axi_if.arsize),
    .arburst(ifd_axi_if.arburst),
    .arvalid(ifd_axi_if.arvalid),
    .arready(ifd_axi_if.arready),
    // write data channel:
    .wdata(ifd_axi_if.wdata),
    .wstrb(ifd_axi_if.wstrb),
    .wlast(ifd_axi_if.wlast),
    .wvalid(ifd_axi_if.wvalid),
    .wready(ifd_axi_if.wready),
    // write resp channel:
    .bid(ifd_axi_if.bid),
    .bresp(ifd_axi_if.bresp),
    .bvalid(ifd_axi_if.bvalid),
    .bready(ifd_axi_if.bready),
    // read resp channel:
    .rid(ifd_axi_if.rid),
    .rdata(ifd_axi_if.rdata),
    .rresp(ifd_axi_if.rresp),
    .rlast(ifd_axi_if.rlast),
    .rvalid(ifd_axi_if.rvalid),
    .rready(ifd_axi_if.rready),

    ///// Tokens:
    .tok_prod_vld(ifd_tok_prod_vld),
    .tok_prod_rdy(ifd_tok_prod_rdy),
    .tok_cons_vld(ifd_tok_cons_vld),
    .tok_cons_rdy(ifd_tok_cons_rdy),

    // MMIO:
    .mm_req(ifd_mm_req),
    .mm_rsp(ifd_mm_rsp),

    //AXIS:
    .axis_m_valid(ifd_axis_if.vld),
    .axis_m_ready(ifd_axis_if.rdy),
    .axis_m_data (ifd_axis_if.data),
    .axis_m_last (ifd_axis_if.last),

    .cid('0),
    .block_id('0),
    .scan_en('0)
  );

  odr #(
    .NR_TOK_PROD(TOK_PROD),
    .NR_TOK_CONS(TOK_CONS)
  ) i_odr (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n),

    .irq(),

    // AXI slave:
    // write address channel:
    .awid(odr_axi_if.awid),
    .awaddr(odr_axi_if.awaddr),
    .awlen(odr_axi_if.awlen),
    .awsize(odr_axi_if.awsize),
    .awburst(odr_axi_if.awburst),
    .awvalid(odr_axi_if.awvalid),
    .awready(odr_axi_if.awready),
    // read address channel:
    .arid(odr_axi_if.arid),
    .araddr(odr_axi_if.araddr),
    .arlen(odr_axi_if.arlen),
    .arsize(odr_axi_if.arsize),
    .arburst(odr_axi_if.arburst),
    .arvalid(odr_axi_if.arvalid),
    .arready(odr_axi_if.arready),
    // write data channel:
    .wdata(odr_axi_if.wdata),
    .wstrb(odr_axi_if.wstrb),
    .wlast(odr_axi_if.wlast),
    .wvalid(odr_axi_if.wvalid),
    .wready(odr_axi_if.wready),
    // write resp channel:
    .bid(odr_axi_if.bid),
    .bresp(odr_axi_if.bresp),
    .bvalid(odr_axi_if.bvalid),
    .bready(odr_axi_if.bready),
    // read resp channel:
    .rid(odr_axi_if.rid),
    .rdata(odr_axi_if.rdata),
    .rresp(odr_axi_if.rresp),
    .rlast(odr_axi_if.rlast),
    .rvalid(odr_axi_if.rvalid),
    .rready(odr_axi_if.rready),

    ///// Tokens:
    .tok_prod_vld(odr_tok_prod_vld),
    .tok_prod_rdy(odr_tok_prod_rdy),
    .tok_cons_vld(odr_tok_cons_vld),
    .tok_cons_rdy(odr_tok_cons_rdy),

    // MMIO:
    .mm_req(odr_mm_req),
    .mm_rsp(odr_mm_rsp),

    //AXIS:
    .axis_s_valid(odr_axis_if.vld),
    .axis_s_ready(odr_axis_if.rdy),
    .axis_s_data (odr_axis_if.data),
    .axis_s_last (odr_axis_if.last),

    .cid('0)
  );
  ////////////////////////////////////////////////////////

  // IFD and ODR tests:

  `include "simple_ifd.sv"
  `include "simple_odr.sv"

  initial begin
    fork
      ifd_test;
      odr_test;
    join
    #100;
    $finish;
  end

  ////////////////////////////////////////////////////////

  /////////////////////////
  task snd_axis_tok(input [DW/8-1:0] strb, input last);
    t_axis_token axis_tok;
    logic [DW-1:0] data;
    axis_tok.last = last;
    axis_tok.strb = strb;
    void'(std::randomize(data));
    axis_tok.data = data;
    mail_odr_axis.put(axis_tok);
  endtask

  ////////////////////////////////////////////////////////
  //////// MMIO response
  mailbox mail_read_req = new();
  mailbox mail_write_req = new();
  integer cur_cnt;

  task ready_drive_handle;
    forever
      @(posedge tb_clk, negedge tb_rst_n) begin
        if (tb_rst_n == 0) begin
          ifd_mm_rsp.ready <= 1;
          odr_mm_rsp.ready <= 1;
          cur_cnt <= 0;
        end else begin
          #0.4;
          ifd_mm_rsp.ready <= ($urandom_range(0, 10) < 2) ? 0 : 1;
          odr_mm_rsp.ready <= ($urandom_range(0, 10) < 2) ? 0 : 1;
          cur_cnt <= cur_cnt + 1;
        end
      end
  endtask

  typedef struct {
    int req_time;
    int addr;
  } tb_req;
  task read_req_handle;
    forever
      @(posedge tb_clk, negedge tb_rst_n) begin
        if (tb_rst_n == 1) begin
          if (ifd_mm_req.valid && ifd_mm_rsp.ready) begin  // valid read req
            tb_req read_req;
            read_req.req_time = cur_cnt;
            read_req.addr = ifd_mm_req.payload.addr;
            mail_read_req.put(read_req);
          end
        end
      end
  endtask

  task write_req_handle;
    forever
      @(posedge tb_clk, negedge tb_rst_n) begin
        if (tb_rst_n == 1) begin
          if (odr_mm_req.valid && odr_mm_rsp.ready) begin  // valid write req
            tb_req write_req;
            write_req.req_time = cur_cnt;
            write_req.addr = odr_mm_req.payload.addr;
            mail_write_req.put(write_req);
          end
        end
      end
  endtask

  `define LL_DELAY 7
  task read_resp_handle;
    tb_req read_req;
    bit [DW-1:0] rand_rdata;
    ifd_mm_rsp.ack <= 'b0;
    forever begin
      // $display("%s: Wait for read request in mailbox", this.name);
      mail_read_req.get(read_req);

      while (cur_cnt - read_req.req_time < `LL_DELAY)
        @(posedge tb_clk);  // delay before returning data
      #0.4;
      void'(std::randomize(rand_rdata));
      ifd_mm_rsp.payload.data <= rand_rdata;
      ifd_mm_rsp.ack <= 'b1;

      @(posedge tb_clk);
      #0.4;
      ifd_mm_rsp.ack <= 'b0;
    end
  endtask

  task write_resp_handle;
    tb_req write_req;
    odr_mm_rsp.ack <= 'b0;
    forever begin
      // $display("%s: Wait for read request in mailbox", this.name);
      mail_write_req.get(write_req);

      while (cur_cnt - write_req.req_time < `LL_DELAY)
        @(posedge tb_clk);  // delay before returning ack
      #0.4;
      odr_mm_rsp.ack <= 'b1;

      @(posedge tb_clk);
      #0.4;
      odr_mm_rsp.ack <= 'b0;
    end
  endtask

  initial begin
    fork
      ready_drive_handle;
      read_req_handle;
      read_resp_handle;
      write_req_handle;
      write_resp_handle;
    join_none
  end
  //////// \MMIO response
  ////////////////////////////////////////////////////////

endmodule
